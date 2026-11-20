"""Build registered Lean modules, recompile their sources, and audit printed axioms.

Only project modules reachable from formalization/RhCertificates.lean are
registered. Each must contain explicit #print axioms declarations. This checks
those declarations and their dependencies; it does not identify a theorem with
research prose or audit every unused declaration in a source file.
"""
import argparse
from pathlib import Path
import re
import subprocess

from check_axiom_report import check


ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formalization"
IMPORT = re.compile(r"^(?:public )?import (RhCertificates(?:\.[A-Za-z0-9_]+)*)$", re.M)
PRINT = re.compile(r"^#print axioms ([A-Za-z0-9_.]+)$", re.M)
NAMESPACE = re.compile(r"^namespace ([A-Za-z0-9_.]+)$", re.M)


def registered_sources():
    seen = set()
    ordered = []

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        source = FORMAL.joinpath(*module.split('.')).with_suffix('.lean')
        content = source.read_text(encoding="utf-8")
        for dependency in IMPORT.findall(content):
            visit(dependency)
        if module != "RhCertificates":
            ordered.append((source, content))

    visit("RhCertificates")
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-build', action='store_true',
                        help='Reuse an already completed project build.')
    args = parser.parse_args()
    wrapper = ROOT / "formalization" / "lakew"
    if not args.no_build:
        subprocess.run([str(wrapper), "build"], cwd=ROOT, check=True)
    count = 0
    for source, content in registered_sources():
        namespaces = NAMESPACE.findall(content)
        if len(namespaces) != 1:
            raise RuntimeError(f"Expected one explicit namespace in {source.name}")
        declarations = PRINT.findall(content)
        if not declarations:
            raise RuntimeError(f"No explicit axiom checks in {source.name}")
        relative = source.relative_to(FORMAL)
        result = subprocess.run([str(wrapper), "env", "lean", str(relative)],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, check=False)
        report = FORMAL / "evidence" / ("replay-" + source.stem + ".txt")
        report.write_text(result.stdout, encoding="utf-8")
        if result.returncode:
            raise RuntimeError(f"Lean failed for {relative}; see {report.relative_to(ROOT)}")
        for declaration in declarations:
            qualified = declaration if '.' in declaration else namespaces[0] + '.' + declaration
            check(result.stdout, qualified)
            count += 1
        print(f"PASS: {relative}: {len(declarations)} explicit axiom checks")
    print(f"PASS: {count} declarations rebuilt and audited with pinned dependencies")


if __name__ == '__main__':
    main()
