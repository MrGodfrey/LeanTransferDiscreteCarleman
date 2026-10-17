module

public import Carleman.Continuous.WeightedNorm
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Actual spatial weighted L² norms

The multiplier acts on mathlib's a.e.-quotiented L² space. No point evaluation
of an equivalence class is asserted: every representative identity is a.e.
The observation multiplier may vanish; a.e. nonvanishing makes the weighted
seminorm a genuine norm. This supports scalar and vector derivative fields.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

structure BoundedMultiplier (ν : Measure Ω) where
  value : Ω → ℝ
  measurable : AEStronglyMeasurable value ν
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounded : ∀ᵐ x ∂ν, |value x| ≤ bound

namespace BoundedMultiplier
variable {ν : Measure Ω} (w : BoundedMultiplier ν)

theorem memLp_smul (u : Lp E 2 ν) : MemLp (fun x => w.value x • u x) 2 ν := by
  apply (Lp.memLp u).of_le_mul (c := w.bound) (w.measurable.smul (Lp.aestronglyMeasurable u))
  filter_upwards [w.bounded] with x hx
  change ‖w.value x • u x‖ ≤ w.bound * ‖u x‖
  simpa only [norm_smul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_right hx (norm_nonneg (u x))

/-- Multiplication by the actual spatial function w on L² equivalence classes. -/
def map (u : Lp E 2 ν) : Lp E 2 ν := (w.memLp_smul u).toLp (fun x => w.value x • u x)

theorem map_ae (u : Lp E 2 ν) : w.map u =ᵐ[ν] (fun x => w.value x • u x) :=
  (w.memLp_smul u).coeFn_toLp

theorem map_add (u v : Lp E 2 ν) : w.map (u+v) = w.map u + w.map v := by
  apply Lp.ext
  filter_upwards [w.map_ae (u+v), w.map_ae u, w.map_ae v,
    Lp.coeFn_add u v, Lp.coeFn_add (w.map u) (w.map v)] with x h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5
  rw [h1, h5, h2, h3, h4, smul_add]

theorem map_smul (c : ℝ) (u : Lp E 2 ν) : w.map (c • u) = c • w.map u := by
  apply Lp.ext
  filter_upwards [w.map_ae (c • u), w.map_ae u, Lp.coeFn_smul c u,
    Lp.coeFn_smul c (w.map u)] with x h1 h2 h3 h4
  simp only [Pi.smul_apply] at h3 h4
  rw [h1, h4, h2, h3, smul_comm]

def linearMap : Lp E 2 ν →ₗ[ℝ] Lp E 2 ν where
  toFun := w.map
  map_add' := w.map_add
  map_smul' := w.map_smul

def seminorm : Seminorm ℝ (Lp E 2 ν) := (normSeminorm ℝ (Lp E 2 ν)).comp w.linearMap

theorem seminorm_apply (u : Lp E 2 ν) : w.seminorm u = ‖w.map u‖ := rfl

theorem seminorm_le (u : Lp E 2 ν) : w.seminorm u ≤ w.bound * ‖u‖ := by
  change ‖w.map u‖ ≤ _
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [w.map_ae u, w.bounded] with x he hb
  rw [he, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- A pointwise spatial weight comparison lifts to the genuine weighted L² norm. -/
theorem seminorm_le_of_weight_le (v : BoundedMultiplier ν) (C : ℝ)
    (h : ∀ᵐ x ∂ν, |w.value x| ≤ C * |v.value x|) (u : Lp E 2 ν) :
    w.seminorm u ≤ C * v.seminorm u := by
  change ‖w.map u‖ ≤ C * ‖v.map u‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [w.map_ae u, v.map_ae u, h] with x hw hv hx
  rw [hw, hv, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hx (norm_nonneg (u x))

theorem seminorm_eq_zero_iff (h : ∀ᵐ x ∂ν, w.value x ≠ 0) (u : Lp E 2 ν) :
    w.seminorm u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    have hz : w.map u = 0 := norm_eq_zero.mp hu
    apply Lp.ext
    filter_upwards [w.map_ae u, h, Lp.coeFn_zero (E := E) (p := 2) (μ := ν)] with x hx hn h0
    rw [hz, h0] at hx
    exact (smul_eq_zero.mp hx.symm).resolve_left hn |>.trans h0.symm
  · rintro rfl
    exact map_zero _

end BoundedMultiplier
end Carleman

@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.BoundedMultiplier
variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ν : Measure Ω} (w : BoundedMultiplier ν)

/-- The square is the spatial integral from the manuscript, on L² classes. -/
theorem seminorm_sq_integral (u : Lp H 2 ν) :
    (w.seminorm u) ^ 2 = ∫ x, |w.value x| ^ 2 * ‖u x‖ ^ 2 ∂ν := by
  rw [w.seminorm_apply, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [w.map_ae u] with x hx
  rw [hx, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow]

theorem integrable_density (u : Lp H 2 ν) :
    Integrable (fun x => |w.value x| ^ 2 * ‖u x‖ ^ 2) ν := by
  have h := (memLp_two_iff_integrable_sq_norm (w.measurable.smul (Lp.aestronglyMeasurable u))).mp (w.memLp_smul u)
  change Integrable (fun x => ‖w.value x • u x‖ ^ 2) ν at h
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow] using h
end Carleman.BoundedMultiplier
