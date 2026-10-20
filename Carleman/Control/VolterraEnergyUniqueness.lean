module

public import Carleman.Control.PivotWeakEnergyIdentity
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman

theorem continuous_volterra_nonneg_eq_zero {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T)) (hn : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hb : ∀ t ∈ Icc 0 T, f t ≤ C*(∫ s in 0..t, f s)) :
    ∀ t ∈ Icc 0 T, f t=0 := by
  let g : TimeGrid := ⟨1,by decide,T,hT⟩
  have hperiod : g.period=T := by simp [g,TimeGrid.period]
  let p : g.TracePath (H := ℝ) := ⟨fun t => f t,by
    apply continuousOn_iff_continuous_domRestrict.mp
    rwa [hperiod]⟩
  let F := g.clampPath p
  have hFe (t : ℝ) (ht : t ∈ Icc 0 T) : F t=f t := by
    exact g.clampPath_on p t (by rwa [hperiod])
  let G := fun t => ∫ s in 0..t, F s
  have hder (t : ℝ) : HasDerivAt G (F t) t :=
    intervalIntegral.integral_hasDerivAt_right (F.continuous.intervalIntegrable _ _)
      (F.continuous.stronglyMeasurableAtFilter volume (𝓝 t)) F.continuous.continuousAt
  have hGe (t : ℝ) (ht : t ∈ Icc 0 T) : G t=∫ s in 0..t, f s := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hFe s ((uIcc_subset_Icc ⟨le_rfl,hT.le⟩ ht) hs)
  have hz : ∀ t ∈ Icc 0 T, G t=0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := C)
      (continuous_iff_continuousAt.mpr fun t => (hder t).continuousAt).continuousOn
      (fun t _ => (hder t).hasDerivWithinAt)
    · simp [G]
    · intro t ht
      have ht' : t ∈ Icc 0 T := ⟨ht.1,ht.2.le⟩
      rw [hFe t ht',Real.norm_of_nonneg (hn t ht')]
      have hh := hb t ht'
      rw [← hGe t ht'] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (Real.le_norm_self (G t)) hC)
  intro t ht
  have hh := hb t ht
  rw [← hGe t ht,hz t ht,mul_zero] at hh
  exact le_antisymm hh (hn t ht)


end Carleman
