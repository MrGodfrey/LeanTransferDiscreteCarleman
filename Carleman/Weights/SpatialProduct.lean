module

public import Carleman.Spatial.WeakProduct
public import Carleman.Weights.CoordinateDerivatives

/-! The weak product rule specialized to the very same allowed exponential
multiplier used by the transfer norms. Only the fixed profile derivative
bound is input; the weight derivative and conjugation formula are proved. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Carleman.SpatialProfile
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ν : Measure E}
  [IsFiniteMeasureOnCompacts ν] (ρ : SpatialProfile ν) {S : Set E}
  (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S) (hρ : ContDiffOn ℝ ∞ ρ.value S)
  (e : E) (M : ℝ) (hM : 0 ≤ M)
  (hb : ∀ᵐ x ∂ν, |fderiv ℝ ρ.value x e| ≤ M)

def directionalMultiplier : BoundedMultiplier ν where
  value x := fderiv ℝ ρ.value x e
  measurable := by
    have hc : ContinuousOn (fun x => fderiv ℝ ρ.value x e) S :=
      (hρ.continuousOn_fderiv_of_isOpen hS (by simp)).clm_apply continuousOn_const
    have hm := hc.aestronglyMeasurable (μ := ν) hS.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hν] at hm
  bound := M
  bound_nonneg := hM
  bounded := hb

def weightDirectionalMultiplier (w : TimeWeight) (τ t : ℝ) : BoundedMultiplier ν where
  value x := w.q t * fderiv ℝ ρ.value x e * (ρ.multiplier w τ t).value x
  measurable := ((ρ.directionalMultiplier hS hν hρ e M hM hb).measurable.const_mul _).mul
    (ρ.multiplier w τ t).measurable
  bound := w.q t * M * (ρ.multiplier w τ t).bound
  bound_nonneg := by positivity [w.pos t, (ρ.multiplier w τ t).bound_nonneg]
  bounded := by
    filter_upwards [hb, (ρ.multiplier w τ t).bounded] with x hx hy
    rw [abs_mul, abs_mul, abs_of_pos (w.pos t)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hx (w.nonneg t)) hy
      (abs_nonneg _) (mul_nonneg (w.nonneg t) hM)

omit [BorelSpace E] [IsFiniteMeasureOnCompacts ν] in
include hρ in
theorem multiplier_smooth (w : TimeWeight) (τ t : ℝ) :
    ContDiffOn ℝ ∞ (ρ.multiplier w τ t).value S :=
  (contDiffOn_const.mul ((hρ.mul contDiffOn_const).exp))

omit [IsFiniteMeasureOnCompacts ν] in
theorem weightDirectionalMultiplier_value (w : TimeWeight) (τ t : ℝ) :
    (ρ.weightDirectionalMultiplier hS hν hρ e M hM hb w τ t).value =ᵐ[ν]
      (fun x => fderiv ℝ (ρ.multiplier w τ t).value x e) := by
  filter_upwards [hν] with x hx
  have hd := (((hρ.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.mul_const
    (w.q t)).exp.const_mul (w.q t^τ)
  change HasFDerivAt (ρ.multiplier w τ t).value _ x at hd
  rw [hd.fderiv]
  simp [weightDirectionalMultiplier, multiplier]
  ring

omit [IsFiniteMeasureOnCompacts ν] in
theorem weightDirectionalMultiplier_map (w : TimeWeight) (τ t : ℝ) (u : Lp ℝ 2 ν) :
    (ρ.weightDirectionalMultiplier hS hν hρ e M hM hb w τ t).map u =
      w.q t • (ρ.directionalMultiplier hS hν hρ e M hM hb).map
        ((ρ.multiplier w τ t).map u) := by
  apply Lp.ext
  filter_upwards [(ρ.weightDirectionalMultiplier hS hν hρ e M hM hb w τ t).map_ae u,
    (ρ.directionalMultiplier hS hν hρ e M hM hb).map_ae ((ρ.multiplier w τ t).map u),
    (ρ.multiplier w τ t).map_ae u,
    Lp.coeFn_smul (w.q t) ((ρ.directionalMultiplier hS hν hρ e M hM hb).map
      ((ρ.multiplier w τ t).map u))] with x h1 h2 h3 h4
  rw [h1, h4]
  change _ = w.q t * _
  rw [h2, h3]
  simp only [directionalMultiplier, weightDirectionalMultiplier, smul_eq_mul]
  ring

/-- Exact weak spatial conjugation: d(sigma u)=sigma du+q(d rho)(sigma u).
Negating the profile and exponent gives the inverse-weight rule. -/
theorem weak_derivative_weighted (w : TimeWeight) (τ t : ℝ) {u v : Lp ℝ 2 ν}
    (hu : IsWeakSpatialDerivative ν S e u v) :
    IsWeakSpatialDerivative ν S e ((ρ.multiplier w τ t).map u)
      ((ρ.multiplier w τ t).map v + w.q t •
        (ρ.directionalMultiplier hS hν hρ e M hM hb).map ((ρ.multiplier w τ t).map u)) := by
  have hh := hu.mul hS hν (ρ.multiplier w τ t)
    (ρ.weightDirectionalMultiplier hS hν hρ e M hM hb w τ t)
    (ρ.multiplier_smooth hρ w τ t)
    (ρ.weightDirectionalMultiplier_value hS hν hρ e M hM hb w τ t)
  rwa [ρ.weightDirectionalMultiplier_map hS hν hρ e M hM hb w τ t] at hh

end Carleman.SpatialProfile
