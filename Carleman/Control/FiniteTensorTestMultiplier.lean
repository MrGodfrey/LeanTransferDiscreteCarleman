module

public import Carleman.Control.TensorTestUniformConsistency
public import Carleman.Control.AveragedPotentialWeakPairing

/-! The original finite smooth tensor test as an actual bounded multiplier; L-infinity errors imply product L2 convergence. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem finite_tensor_test_bounded {S : Set (SpatialCoordinates d)}
    {L : Type*} [Fintype L] (T : ℝ) (η : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ z ∂(volume.restrict (Ioc 0 T)).prod (volume.restrict S),
      |∑ l, η l z.1*(ψ l).value z.2| ≤ B := by
  choose A hA using fun l => isCompact_Icc.exists_bound_of_continuousOn (hη l)
  choose B hB using fun l => (ψ l).compact.exists_bound_of_continuous (ψ l).smooth.continuous
  refine ⟨∑ l, |A l| *|B l|,by positivity,?_⟩
  filter_upwards [quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)] with z hz
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [abs_mul]
  exact mul_le_mul ((hA l z.1 (Ioc_subset_Icc_self hz)).trans (le_abs_self _))
    ((hB l z.2).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

def finiteTensorTestMultiplier {S : Set (SpatialCoordinates d)}
    {L : Type*} [Fintype L] (T : ℝ) (η : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) :
    BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)) where
  value := fun z => ∑ l, η l z.1*(ψ l).value z.2
  measurable := finite_tensor_test_aestronglyMeasurable T η ψ hη
  bound := (finite_tensor_test_bounded T η ψ hη).choose
  bound_nonneg := (finite_tensor_test_bounded T η ψ hη).choose_spec.1
  bounded := (finite_tensor_test_bounded T η ψ hη).choose_spec.2

theorem finiteTensorTestMultiplier_value {S : Set (SpatialCoordinates d)}
    {L : Type*} [Fintype L] (T : ℝ) (η : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (z : ℝ × SpatialCoordinates d) :
    (finiteTensorTestMultiplier T η ψ hη).value z=∑ l, η l z.1*(ψ l).value z.2 := rfl

theorem L2_tendsto_of_Linfty_error {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] (u : ℕ → Lp ℝ 2 ν) (φ : BoundedMultiplier ν)
    (hu : Tendsto (fun n => eLpNorm (fun x => u n x-φ.value x) ⊤ ν) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 φ.toL2) := by
  have he n : (u n-φ.toL2) =ᵐ[ν] fun x => u n x-φ.value x := by
    filter_upwards [Lp.coeFn_sub (u n) φ.toL2,φ.toL2_ae] with x hx hφ
    simpa only [Pi.sub_apply,hφ] using hx
  have htop : Tendsto (fun n => eLpNorm (u n-φ.toL2) ⊤ ν) atTop (𝓝 0) := by
    simpa only [eLpNorm_congr_ae (he _)] using hu
  have hbound n := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := ⊤)
    le_top (Lp.aestronglyMeasurable (u n-φ.toL2))
  norm_num only [ENNReal.toReal_ofNat,ENNReal.toReal_top,div_zero,sub_zero] at hbound
  have hpow : ν univ ^ (1/(2:ℝ)) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top ν univ)
  have hlim : Tendsto (fun n => eLpNorm (u n-φ.toL2) 2 ν) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ => bot_le) hbound
    simpa only [zero_mul,ENNReal.bot_eq_zero] using ENNReal.Tendsto.mul_const htop (Or.inr hpow)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Lp.norm_def,ENNReal.toReal_zero,Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim

end Carleman
