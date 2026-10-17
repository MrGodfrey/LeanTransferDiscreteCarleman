module

public import Carleman.Transfer.Reconstruction
public import Carleman.Periodic.Energy

/-!
# Uniqueness for the shifted discrete equation

The paper's equation `eq:auxEuler` has the mass term `μₙ G zₙ`.
Using (N1)'s injective reconstruction, nonnegativity of `A_h`, and `μₙ > 0`,
we prove uniqueness on all periodic sequences, in both directions. No
projection property, spectral truncation, or extra uniqueness axiom is used.
Existence for a general load is not asserted; the transfer load will have the
prescribed state as an explicit solution.
-/

@[expose] public section

namespace Carleman.Reconstruction

open scoped BigOperators

variable {H X : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {V : Submodule ℝ H} (r : Carleman.Reconstruction V X) (g : TimeGrid)

/-- The spatial and mass terms of `eq:auxEuler`. -/
noncomputable def shiftedSpatial (A : X →ₗ[ℝ] X) (μ : g.Sequence ℝ)
    (z : g.Sequence X) : g.Sequence X :=
  fun i => A (z i) + μ i • r.G (z i)

theorem shiftedSpatial_sub (A : X →ₗ[ℝ] X) (μ : g.Sequence ℝ)
    (u v : g.Sequence X) :
    r.shiftedSpatial g A μ (u - v) =
      r.shiftedSpatial g A μ u - r.shiftedSpatial g A μ v := by
  funext i
  simp only [shiftedSpatial, Pi.sub_apply, map_sub, smul_sub]
  abel

/-- Nonnegative stiffness plus the positive mass detects every nonzero state. -/
theorem eq_zero_of_pairing_shiftedSpatial_nonpos (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i) (z : g.Sequence X)
    (h : g.pairing (r.shiftedSpatial g A μ z) z ≤ 0) : z = 0 := by
  have hn (i : g.Index) :
      0 ≤ inner ℝ (A (z i)) (z i) + μ i * inner ℝ (r.G (z i)) (z i) :=
    add_nonneg (hA _) (mul_nonneg (hμ i).le (r.G_nonneg _))
  have hs : (∑ i, (inner ℝ (A (z i)) (z i) +
      μ i * inner ℝ (r.G (z i)) (z i))) ≤ 0 := by
    apply nonpos_of_mul_nonpos_right _ g.dt_pos
    simpa only [TimeGrid.pairing, shiftedSpatial, inner_add_left,
      real_inner_smul_left] using h
  have heq := le_antisymm hs (Finset.sum_nonneg fun i _ => hn i)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp heq
  funext i
  by_contra hz
  have hp := mul_pos (hμ i) (r.G_positive hR hz)
  have hi := hall i (Finset.mem_univ i)
  linarith [hA (z i)]

private theorem unique_of_time_energy
    (D : g.Sequence X → g.Sequence X)
    (hDsub : ∀ u v, D (u - v) = D u - D v)
    (hDnonneg : ∀ u, 0 ≤ g.pairing (D u) u)
    (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i)
    (u v : g.Sequence X)
    (h : D u + r.shiftedSpatial g A μ u = D v + r.shiftedSpatial g A μ v) :
    u = v := by
  have heq : D (u - v) + r.shiftedSpatial g A μ (u - v) = 0 := by
    rw [hDsub, r.shiftedSpatial_sub]
    have h' := sub_eq_zero.mpr h
    convert h' using 1; abel
  have hzero : g.pairing (D (u - v)) (u - v) +
      g.pairing (r.shiftedSpatial g A μ (u - v)) (u - v) = 0 := by
    have hz := congrArg (fun w => g.pairing w (u - v)) heq
    simpa only [TimeGrid.pairing, Pi.add_apply, inner_add_left,
      Finset.sum_add_distrib, mul_add, Pi.zero_apply, inner_zero_left,
      Finset.sum_const_zero, mul_zero] using hz
  have hz : u - v = 0 := r.eq_zero_of_pairing_shiftedSpatial_nonpos g hR A hA μ hμ
    (u - v) (by linarith [hDnonneg (u - v)])
  exact sub_eq_zero.mp hz

theorem shifted_dPlus_unique (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i)
    (u v : g.Sequence X)
    (h : g.dPlus u + r.shiftedSpatial g A μ u =
      g.dPlus v + r.shiftedSpatial g A μ v) : u = v :=
  r.unique_of_time_energy g g.dPlus g.dPlus_sub g.pairing_dPlus_self_nonneg
    hR A hA μ hμ u v h

theorem shifted_dMinus_unique (hR : Function.Injective r.R)
    (A : X →ₗ[ℝ] X) (hA : ∀ z, 0 ≤ inner ℝ (A z) z)
    (μ : g.Sequence ℝ) (hμ : ∀ i, 0 < μ i)
    (u v : g.Sequence X)
    (h : g.dMinus u + r.shiftedSpatial g A μ u =
      g.dMinus v + r.shiftedSpatial g A μ v) : u = v :=
  r.unique_of_time_energy g g.dMinus g.dMinus_sub g.pairing_dMinus_self_nonneg
    hR A hA μ hμ u v h

end Carleman.Reconstruction
