#!/usr/bin/env python3
"""Check that the nine definitions of Challenge.lean and SpernerCapacity/Defs.lean agree character for
character, and that the two files have the same import lines (the comparator judges the elaborated
terms, which depend on the imports through instance resolution). Exit status 0 means every
definition block and the import list agree."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
NAMES = ["paley", "W", "T7", "IsTournament", "IsTransitiveChain", "transitiveNumber",
         "IsSpernerClique", "spernerCliqueNumber", "capacity"]


def blocks(text):
    """The definition blocks, keyed by name: from the `def`/`noncomputable def` line to the blank
    line after it."""
    out = {}
    lines = text.splitlines()
    for idx, line in enumerate(lines):
        m = re.match(r"^(?:noncomputable )?def (\w+)", line)
        if m and m.group(1) in NAMES:
            end = idx
            while end + 1 < len(lines) and lines[end + 1].strip() != "":
                end += 1
            out[m.group(1)] = "\n".join(lines[idx:end + 1])
    return out


def imports(text):
    return [line.strip() for line in text.splitlines() if re.match(r"^\s*(public\s+)?import\s", line)]


def main():
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    defs = (ROOT / "SpernerCapacity" / "Defs.lean").read_text(encoding="utf-8")
    a, b = blocks(challenge), blocks(defs)
    ok = True
    for name in NAMES:
        if name not in a or name not in b:
            print(f"missing definition block: {name}")
            ok = False
        elif a[name] != b[name]:
            print(f"DIFFERS {name}")
            ok = False
        else:
            print(f"ok    {name}")
    ia, ib = imports(challenge), imports(defs)
    if ia != ib:
        print("the import lists differ:")
        print("  Challenge:", ia)
        print("  Defs:     ", ib)
        ok = False
    else:
        print(f"ok    imports ({len(ia)} lines)")
    print("ALL DEFINITIONS AGREE" if ok else "DEFINITIONS DIFFER")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
