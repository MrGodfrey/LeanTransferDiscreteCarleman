module

public import Carleman.Control.SupportedTimeControl

/-! Every actual supported weak control limit retains a regional representative and the original norm bound. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem hilbert_weak_limit_norm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) (v : H) {C : ℝ} (hb : ∀ n, ‖u n‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z))) :
    ‖v‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hb 0)
  have hi : inner ℝ v v ≤ C*‖v‖ := le_of_tendsto (ht v) (Eventually.of_forall (fun n =>
    (real_inner_le_norm (u n) v).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg v))))
  rw [real_inner_self_eq_norm_sq] at hi
  by_cases hv : ‖v‖=0
  · simpa only [hv] using hC
  · nlinarith [norm_nonneg v]

theorem regional_control_of_weak_limit
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {ν : Measure Ω} (μ : Measure Ξ)
    (ωobs : Set Ω) (hω : MeasurableSet ωobs)
    (u : ℕ → Lp (Lp ℝ 2 ν) 2 μ) (U : Lp (Lp ℝ 2 ν) 2 μ)
    (hu : ∀ n, ∀ᵐ t ∂μ, u n t ∈ Physical.supportedRegionSpace ωobs) {C : ℝ}
    (hb : ∀ n, ‖u n‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ U z))) :
    ∃ v : Lp (Lp ℝ 2 (ν.restrict ωobs)) 2 μ,
      (Physical.restrictRegionCLM (ν := ν) (E := ℝ) ωobs).adjoint.compLp v=U ∧
      ‖v‖=‖U‖ ∧ ‖v‖≤C := by
  have hmem := bochnerKernel_of_weak_tendsto (Physical.restrictRegionCLM (ν := ν) (E := ℝ) ωobsᶜ)
    μ u U (fun n => (mem_bochnerKernelSpace_iff _ _ _).mpr (hu n)) ht
  obtain ⟨v,hv,hn⟩ := supportedBochner_zeroExtension μ ωobs hω U
    ((mem_bochnerKernelSpace_iff _ _ _).mp hmem)
  exact ⟨v,hv,hn,hn.trans_le (hilbert_weak_limit_norm_le u U hb ht)⟩

end Carleman
