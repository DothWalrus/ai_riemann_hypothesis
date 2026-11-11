#!/bin/sh
# Explicit opt-in setup: downloads official tools, pinned dependencies and cache.
set -eu
lean_bootstrap_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$lean_bootstrap_dir/lean-env.sh"

for lean_required in curl git python3; do
    if ! command -v "$lean_required" >/dev/null 2>&1; then
        printf 'Required command not found: %s\n' "$lean_required" >&2
        exit 1
    fi
done

if [ -z "$lean_elan" ]; then
    export ELAN_HOME="$lean_repo_dir/.tools/elan"
    mkdir -p "$lean_repo_dir/.tools/downloads"
    lean_installer="$lean_repo_dir/.tools/downloads/elan-init.sh"
    curl --proto '=https' --tlsv1.2 -fsSL \
        https://elan.lean-lang.org/elan-init.sh -o "$lean_installer"
    sh "$lean_installer" -y --no-modify-path --default-toolchain none
    lean_elan="$ELAN_HOME/bin/elan"
fi

"$lean_elan" toolchain install "$lean_toolchain"
cd "$lean_project_dir"
# Keep the pinned compiler; the committed manifest pins all dependencies.
MATHLIB_NO_CACHE_ON_UPDATE=1 "$lean_elan" run "$lean_toolchain" \
    lake --keep-toolchain update
"$lean_elan" run "$lean_toolchain" lake exe cache get
"$lean_elan" run "$lean_toolchain" lake --no-cache build
"$lean_elan" run "$lean_toolchain" lake env lean RhCertificates/Tangent.lean
