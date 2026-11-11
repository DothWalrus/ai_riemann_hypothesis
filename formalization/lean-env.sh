#!/bin/sh
# Shared environment selection; this file performs no download or installation.
lean_project_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
lean_repo_dir=$(CDPATH= cd -- "$lean_project_dir/.." && pwd)

if [ -n "${ELAN_HOME:-}" ] && [ -x "$ELAN_HOME/bin/elan" ]; then
    lean_elan="$ELAN_HOME/bin/elan"
elif [ -x "$lean_repo_dir/.tools/elan/bin/elan" ]; then
    export ELAN_HOME="$lean_repo_dir/.tools/elan"
    lean_elan="$ELAN_HOME/bin/elan"
elif command -v elan >/dev/null 2>&1; then
    lean_elan=$(command -v elan)
elif [ -x "$HOME/.elan/bin/elan" ]; then
    lean_elan="$HOME/.elan/bin/elan"
else
    lean_elan=''
fi

lean_toolchain=$(tr -d '\r\n' < "$lean_project_dir/lean-toolchain")
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$lean_repo_dir/.tools/cache}"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$lean_repo_dir/.tools/cache/mathlib}"
