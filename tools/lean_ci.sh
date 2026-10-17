#!/usr/bin/env bash
set -euo pipefail
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p .ci
python3 tools/validate_lean_project.py > .ci/mathlib-commit.txt
# Check the resolved dependency, not just a string in the manifest.
task_mathlib_sha="$(git -C .lake/packages/mathlib rev-parse HEAD)"
test "$task_mathlib_sha" = "$(cat .ci/mathlib-commit.txt)"
lake env lean --version > .ci/lean-version.txt
# Bootstrap must create this library target and import every announced completed module.
lake build Carleman
lake env lean tools/CheckAxioms.lean | tee .ci/axioms.txt
