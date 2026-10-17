module

public import Carleman.Transfer.ShiftedScheme

/-!
# The auxiliary load and its discrete solution

The algebra in Section 5, Step 1 (`eq:transfer-load`), uses the original
compatibility `J L = Γ` of (N2). The load map, lift, and right inverse are
ordinary functions: the manuscript does not require their linearity, and their
compatibility equations suffice. This algebra works for any load type; the
paper's normed load space and its weighted bounds enter at the analytic layer.
The scalar shift is an arbitrary node sequence, not a constant.
-/

@[expose] public section

namespace Carleman

variable {H X : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {V : Submodule ℝ H}

/-- The algebraic part of (N2); weighted bounds are separate analytic data. -/
structure LoadInterface (r : Reconstruction V X) (F : Type*) where
  Γ : F → X
  lift : F → H
  compatible : ∀ f, r.J (lift f) = Γ f

namespace LoadInterface

variable {r : Reconstruction V X} {F : Type*}
variable (l : LoadInterface r F) (g : TimeGrid)

/-- Exactly `gⁿ = L_h fⁿ + μₙ R_h zⁿ`, valued in `H`. -/
noncomputable def transferLoad (μ : g.Sequence ℝ) (f : g.Sequence F)
    (z : g.Sequence X) : g.Sequence H :=
  fun i => l.lift (f i) + μ i • r.RH (z i)

theorem J_transferLoad (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X) :
    g.map r.J (l.transferLoad g μ f z) =
      (fun i => l.Γ (f i)) + fun i => μ i • r.G (z i) := by
  funext i
  simp only [TimeGrid.map_apply, transferLoad, map_add, map_smul, l.compatible,
    Pi.add_apply, Reconstruction.G_apply]

theorem state_solves_shifted_dPlus (A : X →ₗ[ℝ] X)
    (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X)
    (hz : g.dPlus z + g.map A z = (fun i => l.Γ (f i))) :
    g.dPlus z + r.shiftedSpatial g A μ z = g.map r.J (l.transferLoad g μ f z) := by
  rw [l.J_transferLoad]
  funext i
  have hi := congrFun hz i
  change g.dPlus z i + A (z i) = l.Γ (f i) at hi
  change g.dPlus z i + (A (z i) + μ i • r.G (z i)) =
    l.Γ (f i) + μ i • r.G (z i)
  rw [← add_assoc, hi]

theorem state_solves_shifted_dMinus (A : X →ₗ[ℝ] X)
    (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X)
    (hz : g.dMinus z + g.map A z = (fun i => l.Γ (f i))) :
    g.dMinus z + r.shiftedSpatial g A μ z = g.map r.J (l.transferLoad g μ f z) := by
  rw [l.J_transferLoad]
  funext i
  have hi := congrFun hz i
  change g.dMinus z i + A (z i) = l.Γ (f i) at hi
  change g.dMinus z i + (A (z i) + μ i • r.G (z i)) =
    l.Γ (f i) + μ i • r.G (z i)
  rw [← add_assoc, hi]

/-- The auxiliary solution is the prescribed state, with uniqueness proved above. -/
theorem auxiliary_dPlus_eq_state (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i)
    (f : g.Sequence F) (z u : g.Sequence X)
    (hz : g.dPlus z + g.map A z = (fun i => l.Γ (f i)))
    (hu : g.dPlus u + r.shiftedSpatial g A μ u =
      g.map r.J (l.transferLoad g μ f z)) : u = z :=
  r.shifted_dPlus_unique g hR A hA μ hμ u z
    (hu.trans (l.state_solves_shifted_dPlus g A μ f z hz).symm)

theorem auxiliary_dMinus_eq_state (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i)
    (f : g.Sequence F) (z u : g.Sequence X)
    (hz : g.dMinus z + g.map A z = (fun i => l.Γ (f i)))
    (hu : g.dMinus u + r.shiftedSpatial g A μ u =
      g.map r.J (l.transferLoad g μ f z)) : u = z :=
  r.shifted_dMinus_unique g hR A hA μ hμ u z
    (hu.trans (l.state_solves_shifted_dMinus g A μ f z hz).symm)

/-- For the chosen transfer load, existence and uniqueness need no extra bridge axiom. -/
theorem existsUnique_auxiliary_dPlus (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i)
    (f : g.Sequence F) (z : g.Sequence X)
    (hz : g.dPlus z + g.map A z = (fun i => l.Γ (f i))) :
    ∃! u : g.Sequence X, g.dPlus u + r.shiftedSpatial g A μ u =
      g.map r.J (l.transferLoad g μ f z) :=
  ⟨z, l.state_solves_shifted_dPlus g A μ f z hz,
    fun u hu => l.auxiliary_dPlus_eq_state g hR A hA μ hμ f z u hz hu⟩

theorem existsUnique_auxiliary_dMinus (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i)
    (f : g.Sequence F) (z : g.Sequence X)
    (hz : g.dMinus z + g.map A z = (fun i => l.Γ (f i))) :
    ∃! u : g.Sequence X, g.dMinus u + r.shiftedSpatial g A μ u =
      g.map r.J (l.transferLoad g μ f z) :=
  ⟨z, l.state_solves_shifted_dMinus g A μ f z hz,
    fun u hu => l.auxiliary_dMinus_eq_state g hR A hA μ hμ f z u hz hu⟩

/-- (N2)'s right inverse supplies a load for every full discrete residual. -/
theorem rightInverse_load (I : X → F) (hI : ∀ z, l.Γ (I z) = z)
    (v : g.Sequence X) : (fun i => l.Γ (I (v i))) = v := by
  funext i
  exact hI (v i)

end LoadInterface
end Carleman
