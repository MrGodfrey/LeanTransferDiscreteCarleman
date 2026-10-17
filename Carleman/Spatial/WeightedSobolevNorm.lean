module

public import Carleman.Spatial.SobolevHilbert
public import Carleman.Spatial.WeakProduct

/-! The manuscript's actual spatial N norm on genuine weak derivative
collections. The underlying conforming space keeps its Sobolev topology. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
namespace WeakSobolevJet
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def weightedSq (q : ℝ) (w : BoundedMultiplier ν) (u : WeakSobolevJet d m ν S) : ℝ :=
  ∑ k : Fin (m+1), (q^(m-k.val) * w.seminorm (field k u))^2

def weightedNorm (q : ℝ) (w : BoundedMultiplier ν) (u : WeakSobolevJet d m ν S) : ℝ :=
  Real.sqrt (weightedSq q w u)

theorem weightedSq_nonneg (q : ℝ) (w : BoundedMultiplier ν) (u : WeakSobolevJet d m ν S) :
    0 ≤ weightedSq q w u := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem weightedNorm_nonneg (q : ℝ) (w : BoundedMultiplier ν) (u : WeakSobolevJet d m ν S) :
    0 ≤ weightedNorm q w u := Real.sqrt_nonneg _

theorem weightedNorm_sq (q : ℝ) (w : BoundedMultiplier ν) (u : WeakSobolevJet d m ν S) :
    (weightedNorm q w u)^2 = weightedSq q w u := Real.sq_sqrt (weightedSq_nonneg q w u)

theorem weighted_component_le {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u : WeakSobolevJet d m ν S) (k : Fin (m+1)) :
    q^(m-k.val) * w.seminorm (field k u) ≤ weightedNorm q w u := by
  apply (sq_le_sq₀ (mul_nonneg (pow_nonneg hq _) (apply_nonneg _ _)) (weightedNorm_nonneg q w u)).mp
  rw [weightedNorm_sq]
  exact Finset.single_le_sum (f := fun j : Fin (m+1) => (q^(m-j.val) * w.seminorm (field j u))^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ k)

theorem weighted_zero_eq (w : BoundedMultiplier ν) (u : WeakSobolevJet d m ν S) :
    w.seminorm (field 0 u) = w.seminorm (value u) := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [w.seminorm_sq_integral, w.seminorm_sq_integral]
  apply integral_congr_ae
  filter_upwards [derivativeComponent_ae Sym.nil (field 0 u)] with x hx
  change value u x = field 0 u x Sym.nil at hx
  have hn : ‖field 0 u x‖^2 = (field 0 u x Sym.nil)^2 := derivativeFiber_zero_norm_sq _
  rw [hn, Real.norm_eq_abs, sq_abs, hx, sq_abs]

theorem weighted_value_le {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u : WeakSobolevJet d m ν S) : q^m * w.seminorm (value u) ≤ weightedNorm q w u := by
  have h := weighted_component_le hq w u 0
  change q^m * w.seminorm (field 0 u) ≤ _ at h
  rw [weighted_zero_eq w u] at h
  exact h

/-- Each term is the norm of the actual scaled, weighted derivative field. -/
theorem weightedSq_eq_sum_norm {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u : WeakSobolevJet d m ν S) :
    weightedSq q w u = ∑ k : Fin (m+1), ‖q^(m-k.val) • w.map (field k u)‖^2 := by
  apply Finset.sum_congr rfl
  intro k _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq _)]
  rfl
end WeakSobolevJet

namespace BoundedMultiplier
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The two actual inverse multipliers cancel in the L² pairing. -/
theorem inner_inverse (w v : BoundedMultiplier ν)
    (h : ∀ᵐ x ∂ν, w.value x * v.value x = 1) (u z : Lp E 2 ν) :
    inner ℝ (w.map u) (v.map z) = inner ℝ u z := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [w.map_ae u, v.map_ae z, h] with x hw hv hx
  rw [hw, hv, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, hx, one_mul]

/-- Multiplication twice realizes σ² exactly, without enlarging the allowed family. -/
theorem inner_map_twice (w : BoundedMultiplier ν) (u : Lp E 2 ν) :
    inner ℝ u (w.map (w.map u)) = ‖w.map u‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [w.map_ae (w.map u), w.map_ae u] with x hw hv
  rw [hw, hv, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
end BoundedMultiplier
end Carleman
