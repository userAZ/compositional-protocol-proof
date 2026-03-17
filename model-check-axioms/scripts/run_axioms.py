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
from subprocess import STDOUT, run
from typing import Optional

AXIOM_RE = re.compile(r"Axiom(\d+)")


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
    failures_lock = Lock()
    print(f"Selected {len(selected)} axiom(s) from {selection_path}.")

    tasks: list[tuple[AxiomEntry, str]] = []
    for entry in selected:
        base_name = unique_name(slugify(f"{entry.family}-{entry.stem}"))
        tasks.append((entry, base_name))

    def run_axiom(entry: AxiomEntry, base_name: str) -> str | None:
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
            return None

        mu_start = time.monotonic()
        mu_result = run(mu_cmd)
        mu_end = time.monotonic()
        if mu_result.returncode != 0:
            return f"mu failed for {entry.m_path}"

        env = os.environ.copy()
        env["CPLUS_INCLUDE_PATH"] = str(include_path)
        gpp_start = time.monotonic()
        gpp_result = run(gpp_cmd, env=env)
        gpp_end = time.monotonic()
        if gpp_result.returncode != 0:
            return f"g++ failed for {cpp_path}"

        with run_log.open("w", encoding="utf-8") as log_handle:
            run_start = time.monotonic()
            run_result = run(run_cmd, cwd=out_dir, stdout=log_handle, stderr=STDOUT)
            run_end = time.monotonic()

        if run_result.returncode != 0:
            return f"run failed for {bin_path} (see {run_log})"

        log_text = run_log.read_text(encoding="utf-8", errors="ignore")
        if any(token in log_text for token in ("Assertion failed", "Segmentation fault", "Aborted", "core dumped")):
            return f"run reported failure for {bin_path} (see {run_log})"

        axiom_end = time.monotonic()
        print(
            "timing:"
            f" mu={mu_end - mu_start:.2f}s"
            f" g++={gpp_end - gpp_start:.2f}s"
            f" run={run_end - run_start:.2f}s"
            f" total={axiom_end - axiom_start:.2f}s"
        )
        return None

    if args.jobs <= 1:
        for entry, base_name in tasks:
            failure = run_axiom(entry, base_name)
            if failure:
                failures.append(failure)
    else:
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            future_map = {
                executor.submit(run_axiom, entry, base_name): (entry, base_name)
                for entry, base_name in tasks
            }
            for future in as_completed(future_map):
                failure = future.result()
                if failure:
                    with failures_lock:
                        failures.append(failure)

    if failures:
        print("\nFailures:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print("\nAll selected axioms completed successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
