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
from subprocess import STDOUT, TimeoutExpired, run
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


@dataclass(frozen=True)
class AxiomEntry:
    family: str
    number: int
    m_path: Path
    stem: str


def slugify(text: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9]+", "-", text).strip("-")
    return slug.lower() or "axiom"


def parse_axiom_number(stem: str) -> Optional[int]:
    match = AXIOM_RE.search(stem)
    if not match:
        return None
    return int(match.group(1))


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
            entries.append(AxiomEntry(family=family, number=number, m_path=m_path, stem=stem))
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

def format_results_table(results: list[tuple[str, str, str]]) -> str:
    rows = sorted(results)
    data = [{"Axiom": name, "Status": status, "Detail": detail} for name, status, detail in rows]

    try:
        from py_markdown_table.markdown_table import markdown_table  # type: ignore

        return markdown_table(data).get_markdown()
    except Exception:
        pass

    # Fallback: simple markdown pipe table.
    lines = ["| Axiom | Status | Detail |", "| --- | --- | --- |"]
    for name, status, detail in rows:
        lines.append(f"| {name} | {status} | {detail} |")
    return "\n".join(lines)


def write_results_html(results: list[tuple[str, str, str]], html_path: Path) -> bool:
    try:
        import pandas as pd  # type: ignore
        from great_tables import GT  # type: ignore
    except Exception:
        return False

    rows = sorted(results)
    df = pd.DataFrame(rows, columns=["Axiom", "Status", "Detail"])
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
        "--timeout-seconds",
        type=int,
        default=0,
        help="Timeout in seconds for each axiom run (0 disables, default: %(default)s)",
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
    parser.add_argument("--dry-run", action="store_true", help="Print commands without running.")
    args = parser.parse_args()

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
    results: list[tuple[str, str, str]] = []
    failures_lock = Lock()
    print(f"Selected {len(selected)} axiom(s) from {selection_path}.")

    tasks: list[tuple[AxiomEntry, str]] = []
    for entry in selected:
        base_name = unique_name(slugify(f"{entry.family}-{entry.stem}"))
        tasks.append((entry, base_name))

    def run_axiom(entry: AxiomEntry, base_name: str) -> tuple[str | None, tuple[str, str, str] | None]:
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

        print(f"\n==> {entry.family} Axiom {entry.number}: {entry.m_path.name}")
        print(f"mu: {' '.join(mu_cmd)}")
        print(f"g++: {' '.join(gpp_cmd)}")
        print(f"run: {' '.join(run_cmd)}")

        if args.dry_run:
            return None, None

        mu_start = time.monotonic()
        mu_result = run(mu_cmd)
        mu_end = time.monotonic()
        if mu_result.returncode != 0:
            return f"mu failed for {entry.m_path}", (entry.m_path.name, "FAIL", "mu failed")

        env = os.environ.copy()
        env["CPLUS_INCLUDE_PATH"] = str(include_path)
        gpp_start = time.monotonic()
        gpp_result = run(gpp_cmd, env=env)
        gpp_end = time.monotonic()
        if gpp_result.returncode != 0:
            return f"g++ failed for {cpp_path}", (entry.m_path.name, "FAIL", "g++ failed")

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
                    "TIMEOUT",
                    f"timeout {args.timeout_seconds}s",
                )
            run_end = time.monotonic()

        if run_result.returncode != 0:
            return f"run failed for {bin_path} (see {run_log})", (
                entry.m_path.name,
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
            return f"run reported failure for {bin_path} (see {run_log})", (
                entry.m_path.name,
                "FAIL",
                detail,
            )

        axiom_end = time.monotonic()
        print(
            "timing:"
            f" mu={mu_end - mu_start:.2f}s"
            f" g++={gpp_end - gpp_start:.2f}s"
            f" run={run_end - run_start:.2f}s"
            f" total={axiom_end - axiom_start:.2f}s"
        )
        if "No error found." in log_text:
            return None, (entry.m_path.name, "PASS", "")
        return None, (entry.m_path.name, "UNKNOWN", "")

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
        print(format_results_table(results))

        if args.table_html:
            html_path = Path(args.table_html)
            if write_results_html(results, html_path):
                print(f"\nHTML table written to {html_path}.")
            else:
                print("\nHTML table not written (great_tables and pandas not available).")

        all_pass = all(status == "PASS" for _, status, _ in results)
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
