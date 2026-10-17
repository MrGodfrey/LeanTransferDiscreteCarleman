#!/usr/bin/env bash
set -euo pipefail
# Run at the repository root. Project versions are committed by M0a, never guessed here.
python3 tools/validate_lean_project.py
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$PWD/.lake/cache}"
if ! command -v elan >/dev/null 2>&1; then
  task_installer="$(mktemp)"
  trap 'rm -f "$task_installer"' EXIT
  curl --proto '=https' --proto-redir '=https' --tlsv1.2 -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$task_installer"
  bash "$task_installer" -y --default-toolchain none --no-modify-path
fi
task_manifest_hash="$(sha256sum lake-manifest.json)"
lean --version
# Fetch the bootstrap module's mathlib imports and their dependencies.
# Additional mathlib cache roots may be passed as arguments during development.
if [ "$#" -eq 0 ]; then
  set -- Mathlib.Algebra.BigOperators.Group.Finset.Basic
fi
lake exe cache get "$@"
test "$task_manifest_hash" = "$(sha256sum lake-manifest.json)"
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "$(python3 tools/validate_lean_project.py)"
