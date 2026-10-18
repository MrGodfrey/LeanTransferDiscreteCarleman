module

public import Carleman.Control.PhysicalParameterChoice
public import Carleman.Spatial.AllowedWeight
public import Carleman.Spatial.MultiplierAlgebra

/-! Physical-time exponential envelopes for genuine spatial L2 weights. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν) (w : TimeWeight)

theorem spatial_weight_upper (rstar t : ℝ) (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar) (u : Lp E 2 ν) :
    (ρ.multiplier w 0 t).seminorm u ≤ Real.exp (-rstar*w.q t)*‖u‖ := by
  have hh := (ρ.multiplier w 0 t).seminorm_le_of_weight_le BoundedMultiplier.one
    (Real.exp (-rstar*w.q t)) (by
      filter_upwards [hneg] with x hx
      simp only [SpatialProfile.multiplier,BoundedMultiplier.one,Real.rpow_zero,one_mul,abs_one,
        mul_one,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx (w.nonneg t))) u
  simpa only [BoundedMultiplier.one_seminorm] using hh

theorem spatial_weight_lower (t : ℝ) (u : Lp E 2 ν) :
    Real.exp (-ρ.bound*w.q t)*‖u‖ ≤ (ρ.multiplier w 0 t).seminorm u := by
  have hh := (BoundedMultiplier.one (ν := ν)).seminorm_le_of_weight_le
    (ρ.multiplier w 0 t) (Real.exp (ρ.bound*w.q t)) (by
      filter_upwards [ρ.bounded] with x hx
      simp only [SpatialProfile.multiplier,BoundedMultiplier.one,Real.rpow_zero,one_mul,abs_one,
        abs_of_pos (Real.exp_pos _)]
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hr := (abs_le.mp hx).1
      nlinarith [w.nonneg t]) u
  rw [BoundedMultiplier.one_seminorm] at hh
  have hl := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-ρ.bound*w.q t)).le
  have he : Real.exp (-ρ.bound*w.q t)*Real.exp (ρ.bound*w.q t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  simpa only [← mul_assoc,he,one_mul] using hl

theorem spatial_weight_upper_sq (rstar t : ℝ) (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar) (u : Lp E 2 ν) :
    ((ρ.multiplier w 0 t).seminorm u)^2 ≤ Real.exp (-2*rstar*w.q t)*‖u‖^2 := by
  have hh := (sq_le_sq₀ (apply_nonneg _ _)
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg u))).mpr (spatial_weight_upper ρ w rstar t hneg u)
  have he : Real.exp (-rstar*w.q t)^2 = Real.exp (-2*rstar*w.q t) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow,he] using hh

theorem spatial_weight_lower_sq (t : ℝ) (u : Lp E 2 ν) :
    Real.exp (-2*ρ.bound*w.q t)*‖u‖^2 ≤ ((ρ.multiplier w 0 t).seminorm u)^2 := by
  have hh := (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg u))
    (apply_nonneg _ _)).mpr (spatial_weight_lower ρ w t u)
  have he : Real.exp (-ρ.bound*w.q t)^2 = Real.exp (-2*ρ.bound*w.q t) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow,he] using hh

theorem physical_spatial_endpoint (g : TimeGrid) (qb S rstar : ℝ) (hqb : 2 ≤ qb)
    (hS : 16*qb ≤ S) (hmesh : S ≤ qb*g.period/(4*g.dt)) (hrstar : 0 < rstar)
    (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar)
    (hw : w.q = physicalWeight qb (qb/S) g.period)
    (i : Fin g.steps) (hi : i ∈ transitionNodes g ((qb/S)*g.period)) (u : Lp E 2 ν) :
    ((ρ.multiplier w 0 (g.nodeTime i)).seminorm u)^2 ≤
      Real.exp (-(2*rstar/Real.sqrt (1+9*Real.pi^2))*S)*‖u‖^2 := by
  have hh := spatial_weight_upper_sq ρ w rstar (g.nodeTime i) hneg u
  have hd := physical_weight_endpoint_decay g qb S (-rstar) rstar hqb hS hmesh hrstar le_rfl i hi
  have he : Real.exp (physicalWeight qb (qb/S) g.period ((i.val:ℝ)*g.dt)*(-rstar))^2 =
      Real.exp (-2*rstar*w.q (g.nodeTime i)) := by
    rw [hw,pow_two,← Real.exp_add]
    congr 1
    dsimp only [TimeGrid.nodeTime]
    ring
  rw [he] at hd
  exact hh.trans (mul_le_mul_of_nonneg_right hd (sq_nonneg _))

theorem physical_spatial_middle (g : TimeGrid) (qb δ : ℝ) (hqb : 0 ≤ qb) (hδ : 0 < δ)
    (hw : w.q = physicalWeight qb δ g.period)
    (i : Fin g.steps) (hi : i ∈ middleNodes g) (u : Lp E 2 ν) :
    Real.exp (-4*ρ.bound*qb)*‖u‖^2 ≤ ((ρ.multiplier w 0 (g.nodeTime i)).seminorm u)^2 := by
  obtain ⟨hl,hr⟩ := (Finset.mem_filter.mp hi).2
  have hq := physicalWeight_middle_upper qb δ g.period ((i.val:ℝ)*g.dt) hqb hδ g.period_pos hl hr
  have he : -4*ρ.bound*qb ≤ -2*ρ.bound*w.q (g.nodeTime i) := by
    rw [hw]
    change -4*ρ.bound*qb ≤ -2*ρ.bound*physicalWeight qb δ g.period ((i.val:ℝ)*g.dt)
    nlinarith [ρ.bound_nonneg]
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (sq_nonneg _)).trans
    (spatial_weight_lower_sq ρ w (g.nodeTime i) u)

end Carleman.Physical
