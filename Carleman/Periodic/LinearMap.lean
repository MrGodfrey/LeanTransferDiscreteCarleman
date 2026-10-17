module

public import Carleman.Periodic.SummationByParts
public import Mathlib.LinearAlgebra.Pi

/-!
# Time-independent maps on the shared periodic sequences

The nodewise action is mathlib's `LinearMap.compLeft`, on `TimeGrid.Sequence`.
Both commutation identities use the existing differences with their original
signs. There is no restriction on the sequence or on the real vector spaces.
-/

@[expose] public section

namespace Carleman.TimeGrid

variable (g : Carleman.TimeGrid)
variable {E F K : Type*}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable [AddCommGroup K] [Module ℝ K]

/-- Nodewise action of a single, time-independent real linear map. -/
abbrev map (L : E →ₗ[ℝ] F) : g.Sequence E →ₗ[ℝ] g.Sequence F :=
  L.compLeft g.Index

@[simp] theorem map_apply (L : E →ₗ[ℝ] F) (u : g.Sequence E) (i : g.Index) :
    g.map L u i = L (u i) := rfl

theorem map_comp (M : F →ₗ[ℝ] K) (L : E →ₗ[ℝ] F) (u : g.Sequence E) :
    g.map (M.comp L) u = g.map M (g.map L u) := rfl

/-- The scalar multiplier may vary with the node; the linear map does not. -/
theorem map_node_smul (L : E →ₗ[ℝ] F) (a : g.Sequence ℝ) (u : g.Sequence E) :
    g.map L (fun i => a i • u i) = fun i => a i • g.map L u i := by
  funext i
  exact L.map_smul (a i) (u i)

theorem dPlus_map (L : E →ₗ[ℝ] F) (u : g.Sequence E) :
    g.dPlus (g.map L u) = g.map L (g.dPlus u) := by
  funext i
  simp only [dPlus, map_apply, map_smul, map_sub]

theorem dMinus_map (L : E →ₗ[ℝ] F) (u : g.Sequence E) :
    g.dMinus (g.map L u) = g.map L (g.dMinus u) := by
  funext i
  simp only [dMinus, map_apply, map_smul, map_sub]

end Carleman.TimeGrid
