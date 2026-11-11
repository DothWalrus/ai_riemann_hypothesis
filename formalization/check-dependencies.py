"""Fail early rather than letting an ordinary Lake build fetch missing sources."""
import json
from pathlib import Path
import subprocess
import sys


def main(project):
    manifest = project / "lake-manifest.json"
    if not manifest.is_file():
        raise SystemExit("Missing Lean manifest; run ./formalization/bootstrap.sh.")
    data = json.loads(manifest.read_text())
    packages = project / data.get("packagesDir", ".lake/packages")
    missing = []
    mismatched = []
    for package in data["packages"]:
        directory = packages / package["name"]
        config = directory / package.get("configFile", "lakefile.lean")
        if not config.is_file():
            missing.append(package["name"])
            continue
        if package.get("type") == "git":
            result = subprocess.run(
                ["git", "-C", str(directory), "rev-parse", "HEAD"],
                capture_output=True, text=True, check=False,
            )
            if result.returncode or result.stdout.strip() != package["rev"]:
                mismatched.append(package["name"])
    if missing:
        raise SystemExit(
            "Missing Lean dependencies: " + ", ".join(missing)
            + ". Run ./formalization/bootstrap.sh explicitly."
        )
    if mismatched:
        raise SystemExit(
            "Lean dependency revisions do not match the manifest: "
            + ", ".join(mismatched)
            + ". Review local changes before running bootstrap; no fetch was attempted."
        )


if __name__ == "__main__":
    main(Path(sys.argv[1]))
