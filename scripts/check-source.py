#!/usr/bin/env python3
"""Reject proof placeholders and prohibited declarations in SpernerCapacity, Solution and Test.

Rejected outside comments and strings: sorry, sorryAx, admit, axiom, unsafe, partial,
native_decide, implemented_by, extern, ofReduceBool (qualified or not), and the kernel-bypass
options debug.skipKernelTC and debug.byAsSorry. Challenge.lean carries the submitted statements
with intentional sorry placeholders, so it is checked for every token except sorry. The
[leanOptions] table of lakefile.toml, if present, may not set any debug. option. The compiled
Test.Axioms module is a separate check.
"""

from pathlib import Path
import re
import sys

FORBIDDEN = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|unsafe|partial|native_decide|implemented_by|extern)\b"
    r"|\b(?:Lean\.)?ofReduceBool\b|\bdebug\.skipKernelTC\b|\bdebug\.byAsSorry\b")
CHALLENGE_FORBIDDEN = re.compile(
    r"\b(?:sorryAx|admit|axiom|unsafe|partial|native_decide|implemented_by|extern)\b"
    r"|\b(?:Lean\.)?ofReduceBool\b|\bdebug\.skipKernelTC\b|\bdebug\.byAsSorry\b")
LAKEFILE_DEBUG = re.compile(r"^\s*debug\.")


def code_without_comments_or_strings(source):
    result = list(source)
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result[index:index + 2] = "  "
                index += 2
            elif pair == "-/":
                depth -= 1
                result[index:index + 2] = "  "
                index += 2
            else:
                result[index] = " " if source[index] != "\n" else "\n"
                index += 1
        elif in_string:
            if source[index] == "\\":
                result[index:index + 2] = "  "
                index += 2
            elif source[index] == '"':
                in_string = False
                result[index] = " "
                index += 1
            else:
                result[index] = " " if source[index] != "\n" else "\n"
                index += 1
        elif pair == "/-":
            depth = 1
            result[index:index + 2] = "  "
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            result[index:end] = " " * (end - index)
            index = end
        elif source[index] == '"':
            in_string = True
            result[index] = " "
            index += 1
        else:
            index += 1
    if depth or in_string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(result)


def violations(source):
    cleaned = code_without_comments_or_strings(source)
    return [(cleaned.count("\n", 0, match.start()) + 1, match.group())
            for match in FORBIDDEN.finditer(cleaned)]


def main():
    root = Path(__file__).resolve().parent.parent
    files = sorted((root / "SpernerCapacity").rglob("*.lean"))
    solution = root / "Solution.lean"
    if not files or not solution.is_file():
        print("Source guard requires SpernerCapacity/*.lean and Solution.lean", file=sys.stderr)
        return 1
    files.append(solution)
    files.extend(sorted((root / "Test").rglob("*.lean")))
    files.append(root / "Test.lean")
    files.append(root / "SpernerCapacity.lean")
    challenge = root / "Challenge.lean"
    failures = 0
    for path in files:
        try:
            found = violations(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, ValueError) as error:
            print(f"{path.relative_to(root)}: {error}", file=sys.stderr)
            failures += 1
            continue
        for line, token in found:
            print(f"{path.relative_to(root)}:{line}: prohibited proof token {token}", file=sys.stderr)
            failures += 1
    try:
        cleaned = code_without_comments_or_strings(challenge.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, ValueError) as error:
        print(f"Challenge.lean: {error}", file=sys.stderr)
        failures += 1
    else:
        for match in CHALLENGE_FORBIDDEN.finditer(cleaned):
            line = cleaned.count("\n", 0, match.start()) + 1
            print(f"Challenge.lean:{line}: prohibited token {match.group()}", file=sys.stderr)
            failures += 1
    lakefile = root / "lakefile.toml"
    try:
        options = lakefile.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        print(f"lakefile.toml: {error}", file=sys.stderr)
        failures += 1
    else:
        section = None
        for number, text in enumerate(options.splitlines(), 1):
            stripped = text.strip()
            if stripped.startswith("["):
                section = stripped
            elif section == "[leanOptions]" and LAKEFILE_DEBUG.match(text):
                print(f"lakefile.toml:{number}: prohibited option {stripped}", file=sys.stderr)
                failures += 1
    if failures:
        return 1
    print(f"Source guard passed for {len(files)} proof files, Challenge.lean (every token except sorry) "
          "and the lakefile options.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
