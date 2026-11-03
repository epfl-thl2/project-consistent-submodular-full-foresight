#!/usr/bin/env python3
"""Build the committed Lean project and audit all exported theorems.

The exported theorems are those listed in `comparator/config.json`, one for
every statement in `ConsistentSubmodular/MainStatements.lean`. The script builds the
project with warnings treated as errors, checks every export against its
stated proposition and prints its axioms with `validation/MainAxioms.lean`, and
rejects any axiom other than `propext`, `Classical.choice`, and `Quot.sound`.
With `--comparator` it also runs Lean's comparator (`scripts/comparator.py`).

Uses only the Python standard library. Run from any directory with Python
3.10+ and the pinned Lean toolchain available through elan/Lake.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
CONFIG = ROOT / "comparator" / "config.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def exported_theorems() -> set[str]:
    config = json.loads(CONFIG.read_text(encoding="utf-8"))
    names = config["theorem_names"]
    if len(names) != len(set(names)):
        raise RuntimeError(f"Duplicate theorem names in {CONFIG}")
    if set(config["permitted_axioms"]) != ALLOWED_AXIOMS:
        raise RuntimeError(f"Unexpected permitted axioms in {CONFIG}")
    challenge = (ROOT / "comparator" / "Challenge.lean").read_text(encoding="utf-8")
    stated = {f"ConsistentSubmodular.{name}" for name in re.findall(r"(?m)^theorem (\w+) :", challenge)}
    if stated != set(names):
        raise RuntimeError("comparator/Challenge.lean and comparator/config.json list different theorems")
    return set(names)


def run_checked(command: list[str], log: Path) -> str:
    print(f"Running: {' '.join(command)}", flush=True)
    with log.open("w", encoding="utf-8") as output:
        result = subprocess.run(
            command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=False
        )
    text = log.read_text(encoding="utf-8")
    if result.returncode:
        print(text, file=sys.stderr)
        raise RuntimeError(f"Command exited with {result.returncode}; see {log}")
    if re.search(r"(?m)^.*\bwarning:", text):
        print(text, file=sys.stderr)
        raise RuntimeError(f"Warnings found; see {log}")
    print(f"Passed; log: {log}", flush=True)
    return text


def audit_axioms(text: str, exports: set[str]) -> dict[str, list[str]]:
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    names = [name for name, _ in matches]
    if len(names) != len(exports) or set(names) != exports:
        raise RuntimeError(
            f"Expected exactly one axiom report per export {sorted(exports)}; found {names}"
        )
    reports = {}
    for name, listed in matches:
        axioms = [axiom.strip() for axiom in listed.split(",") if axiom.strip()]
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise RuntimeError(f"{name} uses unapproved axioms: {sorted(unexpected)}")
        reports[name] = axioms
    return reports


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir", type=Path, default=ROOT / "validation" / "local_runs",
        help="Directory for fresh logs and the JSON receipt (default: validation/local_runs).",
    )
    parser.add_argument(
        "--comparator", action="store_true",
        help="Also check the proofs with Lean's comparator (scripts/comparator.py).",
    )
    args = parser.parse_args()
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    receipt_path = output_dir / "verification.json"
    # A failed new run must not leave an old success receipt in this directory.
    receipt_path.unlink(missing_ok=True)
    if shutil.which("lake") is None:
        raise RuntimeError("Lake was not found. Install elan and follow README.md.")
    exports = exported_theorems()

    run_checked(["lake", "build"], output_dir / "build.log")
    audit = run_checked(
        ["lake", "env", "lean", "validation/MainAxioms.lean"], output_dir / "axioms.log"
    )
    reports = audit_axioms(audit, exports)
    if args.comparator:
        command = [sys.executable, str(ROOT / "scripts" / "comparator.py"),
                   "--output-dir", str(output_dir)]
        print(f"Running: {' '.join(command)}", flush=True)
        if subprocess.run(command, cwd=ROOT, check=False).returncode:
            raise RuntimeError("Comparator check failed")
    inputs = [ROOT / "ConsistentSubmodular.lean",
              *sorted((ROOT / "ConsistentSubmodular").rglob("*.lean"))]
    inputs += sorted((ROOT / "comparator").glob("*"))
    inputs += [ROOT / p for p in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "validation/MainAxioms.lean", "scripts/verify.py", "scripts/comparator.py",
    )]
    receipt = {
        "status": "PASS_BUILD_AND_EXPORTED_AXIOMS"
        + ("_AND_COMPARATOR" if args.comparator else ""),
        "recorded_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "exported_axioms": reports,
        "input_sha256": {
            str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in inputs
        },
    }
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(audit, end="" if audit.endswith("\n") else "\n")
    print(f"PASS: all {len(exports)} exported results use only standard foundational axioms"
          f"{' and pass comparator' if args.comparator else ''}. Receipt: {receipt_path}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, KeyError, ValueError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        raise SystemExit(1)
