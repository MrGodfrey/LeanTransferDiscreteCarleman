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
# Fetch the completed modules' mathlib imports and their dependencies.
# Additional mathlib cache roots may be passed as arguments during development.
if [ "$#" -eq 0 ]; then
  set -- Mathlib.Algebra.BigOperators.Group.Finset.Basic \
    Mathlib.Analysis.InnerProductSpace.Basic Mathlib.Logic.Equiv.Fin.Rotate \
    Mathlib.Analysis.InnerProductSpace.Adjoint \
    Mathlib.MeasureTheory.Function.L2Space Mathlib.MeasureTheory.Measure.Lebesgue.Basic \
    Mathlib.Analysis.Calculus.ContDiff.Basic Mathlib.Analysis.Calculus.Deriv.Basic \
    Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Analysis.Normed.Module.Seminorm.Basic \
    Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic Mathlib.MeasureTheory.Function.Floor \
    Mathlib.MeasureTheory.Integral.Prod Mathlib.Analysis.Calculus.MeanValue \
    Mathlib.Analysis.SpecialFunctions.Log.Deriv Mathlib.Analysis.SpecialFunctions.ExpDeriv \
    Mathlib.Analysis.Normed.Module.Seminorm.Norm Mathlib.Algebra.Field.Periodic \
    Mathlib.Analysis.Calculus.ContDiff.Bounds \
    Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff \
    Mathlib.Analysis.Normed.Lp.MeasurableSpace Mathlib.Data.Fintype.Vector \
    Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas \
    Mathlib.Analysis.Calculus.FDeriv.Measurable Mathlib.Data.Multiset.Sort \
    Mathlib.MeasureTheory.Function.LpSpace.Indicator
fi
lake exe cache get "$@"
test "$task_manifest_hash" = "$(sha256sum lake-manifest.json)"
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "$(python3 tools/validate_lean_project.py)"
