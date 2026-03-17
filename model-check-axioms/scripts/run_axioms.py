#!/usr/bin/env python3
import argparse
import os
import re
import shutil
import time
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock
from dataclasses import dataclass
from pathlib import Path
from subprocess import PIPE, STDOUT, TimeoutExpired, run
from typing import Optional

AXIOM_RE = re.compile(r"Axiom(\d+)")
FAIL_TOKENS = (
    "Assertion failed",
    "Segmentation fault",
    "Aborted",
    "core dumped",
    "Deadlocked state found",
    "The undefined value",
)

GREEN = "\033[0;32m"
YELLOW = "\033[0;33m"
RED = "\033[0;31m"
RESET = "\033[0m"


@dataclass(frozen=True)
class AxiomEntry:
    family: str
    number: int
    m_path: Path
    stem: str
    numbers: tuple[int, ...]


def slugify(text: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9]+", "-", text).strip("-")
    return slug.lower() or "axiom"


def parse_axiom_number(stem: str) -> Optional[int]:
    match = AXIOM_RE.search(stem)
    if not match:
        return None
    return int(match.group(1))

def parse_axiom_numbers(stem: str) -> tuple[int, ...]:
    match = AXIOM_RE.search(stem)
    if not match:
        return ()
    nums = [int(match.group(1))]
    tail = stem[match.end() :]
    nums.extend(int(num) for num in re.findall(r"-and-(\d+)", tail, re.IGNORECASE))
    return tuple(sorted(set(nums)))

def format_axiom_numbers(numbers: tuple[int, ...]) -> str:
    if not numbers:
        return ""
    if len(numbers) == 1:
        return str(numbers[0])
    return ", ".join(str(n) for n in numbers)

def discover_axioms(root: Path) -> list[AxiomEntry]:
    entries: list[AxiomEntry] = []
    for family in ("CXL", "RCCO"):
        axioms_dir = root / family / "axioms"
        if not axioms_dir.is_dir():
            continue
        for m_path in sorted(axioms_dir.glob("*.m")):
            stem = m_path.stem
            number = parse_axiom_number(stem)
            if number is None:
                continue
            numbers = parse_axiom_numbers(stem)
            entries.append(
                AxiomEntry(
                    family=family,
                    number=number,
                    m_path=m_path,
                    stem=stem,
                    numbers=numbers,
                )
            )
    return entries


def load_selection(selection_path: Path, entries: list[AxiomEntry]) -> list[AxiomEntry]:
    if not selection_path.exists():
        return entries

    patterns: list[str] = []
    with selection_path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            patterns.append(line)

    if not patterns:
        return entries

    selected: list[AxiomEntry] = []
    for entry in entries:
        for pat in patterns:
            if pat.endswith(".m"):
                if entry.m_path.name == pat:
                    selected.append(entry)
                    break
                if entry.stem == Path(pat).stem:
                    selected.append(entry)
                    break
                continue

            match = re.match(r"^(CXL|RCCO)\s*[-: ]\s*(\d+)\s*$", pat, re.IGNORECASE)
            if match:
                family = match.group(1).upper()
                number = int(match.group(2))
                if entry.family == family and entry.number == number:
                    selected.append(entry)
                    break
                continue

            match = re.match(r"^(CXL|RCCO)-Axiom(\d+)", pat, re.IGNORECASE)
            if match:
                family = match.group(1).upper()
                number = int(match.group(2))
                if entry.family == family and entry.number == number:
                    selected.append(entry)
                    break
                continue

            if pat.lower() in entry.stem.lower():
                selected.append(entry)
                break

    return selected


def ensure_tool(path: Path, label: str) -> None:
    if not path.exists():
        raise FileNotFoundError(f"{label} not found at {path}")
    if not os.access(path, os.X_OK):
        raise PermissionError(f"{label} is not executable: {path}")


def clean_artifacts(root: Path, out_dir: Path) -> None:
    if out_dir.is_dir():
        for entry in out_dir.iterdir():
            if entry.is_dir():
                shutil.rmtree(entry, ignore_errors=True)
                continue
            entry.unlink(missing_ok=True)

    for family in ("CXL", "RCCO"):
        axioms_dir = root / family / "axioms"
        if not axioms_dir.is_dir():
            continue
        for cpp_file in axioms_dir.glob("*.cpp"):
            cpp_file.unlink(missing_ok=True)

def format_results_table(results: list[tuple[str, str, str, str]]) -> str:
    rows = sorted(results)
    data = [
        {"File": name, "Axiom(s)": axiom_nums, "Status": status, "Detail": detail}
        for name, axiom_nums, status, detail in rows
    ]

    try:
        from py_markdown_table.markdown_table import markdown_table  # type: ignore

        return markdown_table(data).get_markdown()
    except Exception:
        pass

    # Fallback: simple markdown pipe table.
    lines = ["| File | Axiom(s) | Status | Detail |", "| --- | --- | --- | --- |"]
    for name, axiom_nums, status, detail in rows:
        lines.append(f"| {name} | {axiom_nums} | {status} | {detail} |")
    return "\n".join(lines)


def print_results_rich(results: list[tuple[str, str, str, str]]) -> bool:
    try:
        from rich.console import Console  # type: ignore
        from rich.table import Table  # type: ignore
    except Exception:
        return False

    console = Console()
    table = Table(title="Axiom Check Results", show_lines=False)
    table.add_column("File", style="bold")
    table.add_column("Axiom(s)", justify="center")
    table.add_column("Status", justify="center")
    table.add_column("Detail")

    for name, axiom_nums, status, detail in sorted(results):
        if status == "PASS":
            status_cell = "[green]✓ PASS[/green]"
        elif status == "FAIL":
            status_cell = "[red]✗ FAIL[/red]"
        elif status == "TIMEOUT":
            status_cell = "[yellow]⧗ TIMEOUT[/yellow]"
        else:
            status_cell = "[yellow]⚠ UNKNOWN[/yellow]"
        table.add_row(name, axiom_nums, status_cell, detail)

    console.print(table)
    return True

def write_results_html(results: list[tuple[str, str, str, str]], html_path: Path) -> bool:
    try:
        import pandas as pd  # type: ignore
        from great_tables import GT  # type: ignore
    except Exception:
        return False

    rows = sorted(results)
    df = pd.DataFrame(rows, columns=["File", "Axiom(s)", "Status", "Detail"])
    gt = GT(df)
    html_path.parent.mkdir(parents=True, exist_ok=True)
    html_path.write_text(gt.as_raw_html(), encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description="Compile and run Murphi axioms.")
    parser.add_argument(
        "--mu-path",
        default="~/cmurphi5.5.0/src/mu",
        help="Path to Murphi 'mu' executable (default: %(default)s)",
    )
    parser.add_argument(
        "--include-path",
        default="~/cmurphi5.5.0/include",
        help="CPLUS_INCLUDE_PATH for g++ (default: %(default)s)",
    )
    parser.add_argument(
        "--axioms-file",
        default="axioms-to-run.txt",
        help="Path to axioms selection file (default: %(default)s)",
    )
    parser.add_argument(
        "--out-dir",
        default="runs",
        help="Directory to place binaries and run logs (default: %(default)s)",
    )
    parser.add_argument(
        "--m",
        default="5000",
        help="Value for the -m flag passed to the binary (default: %(default)s)",
    )
    parser.add_argument(
        "--memory-per-thread",
        default="",
        help="Alias for --m (memory per run/thread). Overrides --m when set.",
    )
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=0,
        help="Timeout in seconds for each axiom run (0 disables, default: %(default)s)",
    )
    parser.add_argument(
        "--timeout-minutes",
        type=int,
        default=0,
        help="Timeout in minutes for each axiom run (0 disables, overrides --timeout-seconds).",
    )
    parser.add_argument(
        "--clean",
        action="store_true",
        help="Remove existing outputs in runs/ and generated .cpp files before running.",
    )
    parser.add_argument(
        "--table-html",
        default="",
        help="Write an HTML results table to the given path (requires great_tables + pandas).",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="Number of axioms to run in parallel (default: %(default)s)",
    )
    parser.add_argument(
        "--threads",
        type=int,
        default=0,
        help="Alias for --jobs (parallel runs). Overrides --jobs when set.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Print commands without running.")
    parser.add_argument(
        "--print-parsed",
        action="store_true",
        help="Print a table of parsed axiom numbers and exit.",
    )
    args = parser.parse_args()
    if args.timeout_minutes:
        args.timeout_seconds = args.timeout_minutes * 60
    if args.threads:
        args.jobs = args.threads
    if args.memory_per_thread:
        args.m = args.memory_per_thread

    root = Path(__file__).resolve().parents[1]
    mu_path = Path(os.path.expanduser(args.mu_path))
    include_path = Path(os.path.expanduser(args.include_path))
    out_dir = Path(args.out_dir)
    selection_path = Path(args.axioms_file)

    try:
        ensure_tool(mu_path, "mu")
    except (FileNotFoundError, PermissionError) as exc:
        print(f"Error: {exc}")
        return 2

    if shutil.which("g++") is None:
        print("Error: g++ not found on PATH")
        return 2

    entries = discover_axioms(root)
    if not entries:
        print("Error: no axioms discovered")
        return 2

    selected = load_selection(selection_path, entries)
    if not selected:
        print("Error: no axioms matched selection file")
        return 2

    if args.print_parsed:
        parsed_rows = [
            (entry.m_path.name, format_axiom_numbers(entry.numbers), "PARSED", "")
            for entry in selected
        ]
        print("\nParsed Axiom(s):")
        if not print_results_rich(parsed_rows):
            print(format_results_table(parsed_rows))
        return 0

    out_dir.mkdir(parents=True, exist_ok=True)
    if args.clean:
        clean_artifacts(root, out_dir)
    trace_dir = out_dir / "trace-mu"
    trace_dir.mkdir(parents=True, exist_ok=True)

    used_names: dict[str, int] = {}

    def unique_name(base: str) -> str:
        count = used_names.get(base, 0)
        used_names[base] = count + 1
        if count == 0:
            return base
        return f"{base}-{count + 1}"

    failures: list[str] = []
    results: list[tuple[str, str, str, str]] = []
    failures_lock = Lock()
    print(f"Selected {len(selected)} axiom(s) from {selection_path}.")

    tasks: list[tuple[AxiomEntry, str]] = []
    for entry in selected:
        base_name = unique_name(slugify(f"{entry.family}-{entry.stem}"))
        tasks.append((entry, base_name))

    def run_axiom(entry: AxiomEntry, base_name: str) -> tuple[str | None, tuple[str, str, str, str] | None]:
        axiom_start = time.monotonic()
        cpp_path = entry.m_path.with_suffix(".cpp")
        bin_path = out_dir / base_name
        run_log = out_dir / f"{base_name}.run"

        mu_cmd = [str(mu_path), "-c", str(entry.m_path)]
        gpp_cmd = [
            "g++",
            "-std=c++11",
            "-O3",
            str(cpp_path),
            "-o",
            str(bin_path),
        ]
        run_cmd = [
            f"./{bin_path.name}",
            "-vbfs",
            f"-m{args.m}",
            "-td",
            "-p5",
            "-d",
            trace_dir.name,
        ]
        if entry.family == "RCCO" and entry.number == 4:
            run_cmd.append("-sym1")

        axiom_nums = format_axiom_numbers(entry.numbers)
        axiom_label = f"Axiom(s) {axiom_nums}" if axiom_nums else "Axiom(s) ?"
        print(f"\n==> Launching Murphi Model Checking Thread: {entry.family} {axiom_label}: {entry.m_path.name}")

        if args.dry_run:
            return None, None

        mu_start = time.monotonic()
        mu_result = run(mu_cmd, stdout=PIPE, stderr=STDOUT, text=True)
        mu_end = time.monotonic()
        if mu_result.returncode != 0:
            print(mu_result.stdout.strip())
            print(
                f"Thread finished ({entry.family} {axiom_label}): "
                f"{RED}✗ FAIL{RESET} (mu)"
            )
            return f"mu failed for {entry.m_path}", (entry.m_path.name, axiom_nums, "FAIL", "mu failed")

        env = os.environ.copy()
        env["CPLUS_INCLUDE_PATH"] = str(include_path)
        gpp_start = time.monotonic()
        gpp_result = run(gpp_cmd, env=env, stdout=PIPE, stderr=STDOUT, text=True)
        gpp_end = time.monotonic()
        if gpp_result.returncode != 0:
            print(gpp_result.stdout.strip())
            print(
                f"Thread finished ({entry.family} {axiom_label}): "
                f"{RED}✗ FAIL{RESET} (g++)"
            )
            return f"g++ failed for {cpp_path}", (entry.m_path.name, axiom_nums, "FAIL", "g++ failed")

        with run_log.open("w", encoding="utf-8") as log_handle:
            run_start = time.monotonic()
            try:
                run_result = run(
                    run_cmd,
                    cwd=out_dir,
                    stdout=log_handle,
                    stderr=STDOUT,
                    timeout=args.timeout_seconds or None,
                )
            except TimeoutExpired:
                run_end = time.monotonic()
                log_handle.write(f"\nTimed out after {args.timeout_seconds}s.\n")
                return f"run timed out for {bin_path} (see {run_log})", (
                    entry.m_path.name,
                    axiom_nums,
                    "TIMEOUT",
                    f"timeout {args.timeout_seconds}s",
                )
            run_end = time.monotonic()

        if run_result.returncode != 0:
            print(
                f"Thread finished ({entry.family} {axiom_label}): "
                f"{RED}✗ FAIL{RESET} (run exit {run_result.returncode})"
            )
            return f"run failed for {bin_path} (see {run_log})", (
                entry.m_path.name,
                axiom_nums,
                "FAIL",
                "nonzero exit",
            )

        log_text = run_log.read_text(encoding="utf-8", errors="ignore")
        if any(token in log_text for token in FAIL_TOKENS):
            detail = "failure"
            if "Assertion failed" in log_text:
                detail = "assertion failed"
            elif "Deadlocked state found" in log_text:
                detail = "deadlock"
            elif "The undefined value" in log_text:
                detail = "undefined value"
            print(
                f"Thread finished ({entry.family} {axiom_label}): "
                f"{RED}✗ FAIL{RESET} ({detail})"
            )
            return f"run reported failure for {bin_path} (see {run_log})", (
                entry.m_path.name,
                axiom_nums,
                "FAIL",
                detail,
            )

        axiom_end = time.monotonic()
        if "No error found." in log_text:
            status_text = f"{GREEN}✓ PASS{RESET}"
            result = (entry.m_path.name, axiom_nums, "PASS", "")
        else:
            status_text = f"{YELLOW}⚠ UNKNOWN{RESET}"
            result = (entry.m_path.name, axiom_nums, "UNKNOWN", "")

        print(
            f"Thread finished ({entry.family} {axiom_label}): {status_text}, "
            f"Timing: mu={mu_end - mu_start:.2f}s"
            f" g++={gpp_end - gpp_start:.2f}s"
            f" run={run_end - run_start:.2f}s"
            f" total={axiom_end - axiom_start:.2f}s"
        )
        return None, result

    if args.jobs <= 1:
        for entry, base_name in tasks:
            failure, result = run_axiom(entry, base_name)
            if failure:
                failures.append(failure)
            if result:
                results.append(result)
    else:
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            future_map = {
                executor.submit(run_axiom, entry, base_name): (entry, base_name)
                for entry, base_name in tasks
            }
            for future in as_completed(future_map):
                failure, result = future.result()
                with failures_lock:
                    if failure:
                        failures.append(failure)
                    if result:
                        results.append(result)

    if results:
        print("\nResults:")
        if not print_results_rich(results):
            print(format_results_table(results))

        if args.table_html:
            html_path = Path(args.table_html)
            if write_results_html(results, html_path):
                print(f"\nHTML table written to {html_path}.")
            else:
                print("\nHTML table not written (great_tables and pandas not available).")

        all_pass = all(status == "PASS" for _, _, status, _ in results)
        if all_pass:
            print("\nAll axioms successfully model checked.")
        else:
            print("\nNot all axioms successfully model checked.")

    if failures:
        print("\nFailures:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print("\nAll selected axioms completed successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
