#!/usr/bin/env python3
"""Build all modules, audit project axioms, and compile the usage example."""

from pathlib import Path
import argparse
import os
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake-workspace", type=Path, default=ROOT,
                        help="Use a consuming Lake workspace and its dependency cache")
    args = parser.parse_args()
    modules = {".".join(p.relative_to(ROOT).with_suffix("").parts)
               for p in (ROOT / "DivisionFree").rglob("*.lean")}
    imports = set(re.findall(r"^import\s+(DivisionFree\.[\w.]+)\s*$",
                             (ROOT / "DivisionFree.lean").read_text(), re.MULTILINE))
    if modules != imports:
        raise SystemExit(f"Root imports do not match source modules: {modules ^ imports}")
    print(f"Checking {len(modules)} source modules.", flush=True)
    subprocess.run(["lake", "build", "DivisionFree"], cwd=args.lake_workspace, check=True)
    # A consuming workspace can resolve a different dependency with the same
    # module name. Check Lean's search order before trusting the axiom audit.
    lean_path = subprocess.check_output(
        ["lake", "env", sys.executable, "-c",
         "import os; print(os.environ.get('LEAN_PATH', ''))"],
        cwd=args.lake_workspace, text=True).strip()
    expected = (ROOT / ".lake/build/lib/lean/DivisionFree.olean").resolve()
    resolved = next((candidate.resolve() for entry in lean_path.split(os.pathsep)
                     if entry and (candidate := Path(entry) / "DivisionFree.olean").is_file()),
                    None)
    if resolved != expected:
        raise SystemExit(f"Workspace resolves DivisionFree to {resolved}, expected {expected}")
    subprocess.run(["lake", "env", "lean", str(ROOT / "scripts/Audit.lean")],
                   cwd=args.lake_workspace, check=True)
    subprocess.run(["lake", "env", "lean", str(ROOT / "examples/FullMultiplication.lean")],
                   cwd=args.lake_workspace, check=True)


if __name__ == "__main__":
    main()
