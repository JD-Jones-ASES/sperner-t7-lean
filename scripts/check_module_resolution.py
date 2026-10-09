#!/usr/bin/env python3
"""Reject submission modules shadowed by dependencies in Lake's source path.

Run with `lake env python3 scripts/check_module_resolution.py`. Palomar resolves
configured modules by the first matching file in LEAN_SRC_PATH before compiling
its independent challenge. A successful ordinary build alone does not check this.
"""
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    source_path = os.environ.get("LEAN_SRC_PATH", "")
    if not source_path:
        raise SystemExit("Run this check through lake env; LEAN_SRC_PATH is missing.")
    config = json.loads((ROOT / "comparator.json").read_text())
    for key in ("challenge_module", "solution_module"):
        module = config[key]
        suffix = Path(*module.split(".")).with_suffix(".lean")
        candidates = [Path(p) / suffix for p in source_path.split(os.pathsep) if p]
        resolved = next((p.resolve() for p in candidates if p.is_file()), None)
        expected = (ROOT / suffix).resolve()
        if resolved != expected:
            raise SystemExit(f"{key} {module}: expected {expected}, resolved {resolved}")
        print(f"Module source: {module} -> {resolved.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
