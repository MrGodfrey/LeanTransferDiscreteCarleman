module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Periodic primitives built from the actual interval integral. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman

theorem exists_continuous_periodic_extension {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (he : f 0=f T) :
    ∃ g : ℝ → ℝ, Continuous g ∧ Function.Periodic g T ∧ EqOn g f (Icc 0 T) := by
  let : Fact (0 < T) := ⟨hT⟩
  let g : ℝ → ℝ := fun t => AddCircle.liftIco T 0 f (t : AddCircle T)
  have hc : Continuous g := (AddCircle.liftIco_zero_continuous he hf).comp (AddCircle.continuous_mk' T)
  have hp : Function.Periodic g T := by
    intro t
    simp only [g,AddCircle.coe_add,AddCircle.coe_period,add_zero]
  refine ⟨g,hc,hp,?_⟩
  intro t ht
  rcases ht.2.eq_or_lt with heq | hlt
  · rw [heq,show g T=g 0 by simpa using hp 0]
    exact (AddCircle.liftIco_zero_coe_apply (show (0:ℝ) ∈ Ico 0 T from ⟨le_rfl,hT⟩)).trans he
  · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1,hlt⟩

theorem periodic_primitive_of_interval {T : ℝ} (hT : 0 < T) {F f : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 T)) (hf : Continuous f) (hp : Function.Periodic f T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt F (f t) (Icc 0 T) t) (he : F 0=F T) :
    ∃ G : ℝ → ℝ, (∀ t, HasDerivAt G (f t) t) ∧ Function.Periodic G T ∧ EqOn G F (Icc 0 T) := by
  have hint (t : ℝ) (ht : t ∈ Icc 0 T) : (∫ s in 0..t, f s)=F t-F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hF.mono (Icc_subset_Icc le_rfl ht.2))
    · intro s hs
      exact (hd s ⟨hs.1.le,hs.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))
    · exact hf.intervalIntegrable _ _
  have hz : (∫ s in 0..T, f s)=0 := by rw [hint T ⟨hT.le,le_rfl⟩,← he,sub_self]
  let G := fun t => F 0+∫ s in 0..t, f s
  refine ⟨G,?_,?_,?_⟩
  · intro t
    simpa only [zero_add] using
      (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
        hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_add (F 0)
  · intro t
    dsimp only [G]
    rw [hp.intervalIntegral_add_eq_add 0 t (fun a b => hf.intervalIntegrable a b),zero_add,hz,add_zero]
  · intro t ht
    dsimp only [G]
    rw [hint t ht]
    ring

end Carleman
