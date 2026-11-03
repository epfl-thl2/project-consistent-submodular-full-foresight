#!/usr/bin/env python3
"""Check the proofs with Lean's comparator.

Comparator (https://github.com/leanprover/comparator) builds the challenge
module `comparator/Challenge.lean`, which states every theorem of the paper
with its proof left open, and the solution module `comparator/Solution.lean`,
which imports the proofs. It exports both environments with lean4export and
checks that every theorem listed in `comparator/config.json`

1. has exactly the statement of the challenge, including every definition the
   statement depends on,
2. uses no axioms beyond `propext`, `Quot.sound`, and `Classical.choice`, and
3. is accepted by the Lean kernel, replayed from the exported declarations.

The tools are pinned to versions for Lean 4.30.0-rc1 and built on first use
under `.lake/comparator-tools/`. Comparator sandboxes the builds with landrun,
which needs Linux. On other systems (macOS) this script substitutes a
pass-through shim, as comparator's own `scripts/fake-landrun.sh` does, and says
so: the three checks above are unchanged, but the builds are not sandboxed.
That is acceptable here because the solution is this repository's own code.

Uses only the Python standard library.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
CONFIG = ROOT / "comparator" / "config.json"
TOOLS = {
    # Tag v4.30.0-rc1, the exporter for this project's Lean version.
    "lean4export": (
        "https://github.com/leanprover/lean4export.git",
        "fb517af7d71065b28c256348afdf764308acc369",
        Path(".lake/build/bin/lean4export"),
    ),
    # The last comparator commit on Lean v4.30.0-rc1 (comparator was later
    # merged into Lean core as `lake comparator`, from Lean v4.35.0 on).
    "comparator": (
        "https://github.com/leanprover/comparator.git",
        "0ff36dde148dfea82dbdcf3baf91d6e1a8195554",
        Path(".lake/build/bin/comparator"),
    ),
}


def run(command: list[str], cwd: Path, log=None, env=None) -> None:
    print(f"Running: {' '.join(command)}  (in {cwd})", flush=True)
    result = subprocess.run(command, cwd=cwd, env=env, check=False,
                            stdout=log, stderr=subprocess.STDOUT if log else None)
    if result.returncode:
        raise RuntimeError(f"{command[0]} exited with {result.returncode}")


def prepare_tool(name: str, tools_dir: Path) -> Path:
    url, commit, binary = TOOLS[name]
    checkout = tools_dir / name
    if not checkout.exists():
        run(["git", "clone", "--quiet", url, str(checkout)], tools_dir)
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=checkout, check=True,
                          capture_output=True, text=True).stdout.strip()
    if head != commit:
        run(["git", "fetch", "--quiet", "origin"], checkout)
        run(["git", "checkout", "--quiet", commit], checkout)
    if not (checkout / binary).exists():
        run(["lake", "build"], checkout)
    return checkout


# A pass-through stand-in for landrun, modeled on comparator's later
# `scripts/fake-landrun.sh`: it drops landrun's own flags and runs the command
# without a sandbox.
LANDRUN_SHIM = """#!/usr/bin/env bash
set -euo pipefail
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; break ;;
    --ro|--rox|--rw|--rwx|--env|--bind-tcp|--connect-tcp|--log-level) shift 2 ;;
    -*) shift ;;
    *) break ;;
  esac
done
exec "$@"
"""


def landrun_dir(tools_dir: Path) -> tuple[Path | None, bool]:
    """Return a directory to prepend to PATH for landrun, and whether it sandboxes."""
    if shutil.which("landrun"):
        return None, True
    shim_dir = tools_dir / "landrun-shim"
    shim_dir.mkdir(exist_ok=True)
    shim = shim_dir / "landrun"
    shim.write_text(LANDRUN_SHIM, encoding="utf-8")
    shim.chmod(shim.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    return shim_dir, False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--config", type=Path, default=CONFIG,
        help="Comparator configuration (default: comparator/config.json).",
    )
    parser.add_argument(
        "--output-dir", type=Path, default=ROOT / "validation" / "local_runs",
        help="Directory for the comparator log (default: validation/local_runs).",
    )
    args = parser.parse_args()
    config = args.config.resolve()
    if shutil.which("lake") is None:
        raise RuntimeError("Lake was not found. Install elan and follow README.md.")
    tools_dir = ROOT / ".lake" / "comparator-tools"
    tools_dir.mkdir(parents=True, exist_ok=True)
    exporter = prepare_tool("lean4export", tools_dir)
    comparator = prepare_tool("comparator", tools_dir)
    shim_dir, sandboxed = landrun_dir(tools_dir)
    if not sandboxed:
        print("WARNING: landrun (Linux only) was not found; using a pass-through "
              "shim. The checks are unchanged, but the builds are not sandboxed.",
              file=sys.stderr, flush=True)

    env = dict(os.environ)
    paths = [str(exporter / TOOLS["lean4export"][2].parent)]
    if shim_dir is not None:
        paths.append(str(shim_dir))
    env["PATH"] = os.pathsep.join(paths + [env.get("PATH", "")])

    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    log_path = output_dir / "comparator.log"
    with log_path.open("w", encoding="utf-8") as log:
        try:
            run(["lake", "env", str(comparator / TOOLS["comparator"][2]), str(config)],
                ROOT, log=log, env=env)
        finally:
            log.flush()
    text = log_path.read_text(encoding="utf-8")
    print(text, end="" if text.endswith("\n") else "\n")
    if "Your solution is okay!" not in text:
        raise RuntimeError(f"Comparator did not accept the solution; see {log_path}")
    print(f"PASS: comparator accepts every theorem in {config.name}"
          f"{'' if sandboxed else ' (unsandboxed run)'}. Log: {log_path}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"Comparator check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
