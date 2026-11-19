"""Check disclosed axiom lists for explicitly named Lean declarations.

This checks a Lean-generated report after successful compilation. It does
not prove that arbitrary repository prose corresponds to the Lean theorem.
"""
import argparse
from pathlib import Path
import re
import sys

EXPECTED = "RhCertificates.tangent_negative"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def check(text, expected=EXPECTED):
    pattern = "'" + re.escape(expected) + r"' depends on axioms:\s*\[([^\]]*)\]"
    matches = re.findall(pattern, text)
    independent = f"'{expected}' does not depend on any axioms" in text
    if not matches and not independent:
        raise ValueError("Expected Lean axiom report was not found: " + expected)
    for match in matches:
        names = {name.strip() for name in match.split(',') if name.strip()}
        unexpected = names - ALLOWED
        if unexpected:
            raise ValueError("Unexpected axioms: " + ", ".join(sorted(unexpected)))
    return True


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('report', type=Path)
    parser.add_argument('--theorem', action='append', dest='theorems',
                        help='Exact declaration name; repeat to require multiple reports.')
    args = parser.parse_args()
    try:
        report = args.report.read_text(encoding='utf-8')
        for theorem in args.theorems or [EXPECTED]:
            check(report, theorem)
    except (OSError, ValueError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        raise SystemExit(1)
    print('PASS: all requested declarations report only the allowed logical foundations.')
