#!/usr/bin/env python3
"""Check that every theorem header of Challenge.lean (`theorem NAME ... :=`, whitespace normalised,
comments removed) appears verbatim in Solution.lean, and that Solution.lean does not import Challenge.
Exit status 0 means every header agrees."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def headers(text):
    out = {}
    for m in re.finditer(r"\btheorem\s+([\w.']+)(.*?):=", strip_comments(text), flags=re.S):
        out[m.group(1)] = " ".join(m.group(2).split())
    return out


def main():
    chal = headers((ROOT / "Challenge.lean").read_text(encoding="utf-8"))
    sol_text = (ROOT / "Solution.lean").read_text(encoding="utf-8")
    sol = headers(sol_text)
    ok = True
    if re.search(r"^\s*(public\s+)?import\s+Challenge\b", sol_text, flags=re.M):
        print("Solution.lean imports Challenge")
        ok = False
    if not chal:
        print("no theorem headers found in Challenge.lean")
        ok = False
    for name, head in chal.items():
        if name not in sol:
            print(f"missing in Solution.lean: {name}")
            ok = False
        elif sol[name] != head:
            print(f"DIFFERS {name}\n  challenge: {head}\n  solution:  {sol[name]}")
            ok = False
        else:
            print(f"ok    {name}")
    print(f"{len(chal)} headers compared")
    print("ALL STATEMENTS AGREE" if ok else "STATEMENTS DIFFER")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
