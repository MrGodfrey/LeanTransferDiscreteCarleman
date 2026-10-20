module

public import Carleman.Spatial.WeakWeightedForm

/-! The actual finite sum of all coefficient-weighted weak derivative pairings.
The weighted upper constant depends only on coefficient bounds. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace Carleman
abbrev MultiDerivativeIndex (d m : ℕ) := Σ k : Fin (m+1), Sym (Fin d) k.val

variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

-- Select the existing strong-dual topology instance explicitly.
local instance : ContinuousAdd (WeakSobolevJet d m ν S →L[ℝ] ℝ) :=
  (inferInstance : IsTopologicalAddGroup (WeakSobolevJet d m ν S →L[ℝ] ℝ)).toContinuousAdd

def jetScalarComponent (α : MultiDerivativeIndex d m) :
    WeakSobolevJet d m ν S →L[ℝ] Lp ℝ 2 ν :=
  (derivativeComponentCLM α.2).comp (WeakSobolevJet.fieldCLM α.1)

def coefficientJetForm (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier ν) :
    WeakSobolevJet d m ν S →L[ℝ] WeakSobolevJet d m ν S →L[ℝ] ℝ :=
  ∑ α, ∑ β, (innerSL ℝ).bilinearComp ((a α β).continuousLinearMap.comp (jetScalarComponent β))
    (jetScalarComponent α)

theorem coefficientJetForm_apply
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier ν)
    (u v : WeakSobolevJet d m ν S) :
    coefficientJetForm a u v=∑ α, ∑ β, inner ℝ ((a α β).map (jetScalarComponent β u)) (jetScalarComponent α v) := by
  simp only [coefficientJetForm,sum_apply,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply]
  rfl

theorem coefficientJetForm_integral
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier ν)
    (u v : WeakSobolevJet d m ν S) :
    coefficientJetForm a u v=∑ α, ∑ β, ∫ x,
      (a α β).value x*(jetScalarComponent β u x)*(jetScalarComponent α v x) ∂ν := by
  rw [coefficientJetForm_apply]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(a α β).map_ae (jetScalarComponent β u)] with x hx
  rw [hx]
  simp only [RCLike.inner_apply,conj_trivial,smul_eq_mul]
  ring

theorem coefficientJetForm_symmetric
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier ν)
    (hsym : ∀ α β, (a α β).value =ᵐ[ν] (a β α).value)
    (u v : WeakSobolevJet d m ν S) : coefficientJetForm a u v=coefficientJetForm a v u := by
  rw [coefficientJetForm_apply,coefficientJetForm_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  have he : (a β α).map (jetScalarComponent α u)=(a α β).map (jetScalarComponent α u) := by
    apply Lp.ext
    filter_upwards [(a β α).map_ae (jetScalarComponent α u),(a α β).map_ae (jetScalarComponent α u),hsym β α]
      with x hx hy ha
    rw [hx,hy,ha]
  rw [he,BoundedMultiplier.inner_map_left]
  exact real_inner_comm _ _

theorem jetScalarComponent_weighted_le {q : ℝ} (hq : 1 ≤ q)
    (w : BoundedMultiplier ν) (u : WeakSobolevJet d m ν S) (α : MultiDerivativeIndex d m) :
    w.seminorm (jetScalarComponent α u) ≤ WeakSobolevJet.weightedNorm q w u := by
  have hcomp := derivativeComponent_weighted_norm_le w α.2 (WeakSobolevJet.field α.1 u)
  have hpow : 1 ≤ q^(m-α.1.val) := one_le_pow₀ hq
  exact hcomp.trans ((le_mul_of_one_le_left (apply_nonneg _ _) hpow).trans
    (WeakSobolevJet.weighted_component_le (zero_le_one.trans hq) w u α.1))

theorem coefficientJetForm_weighted_upper
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier ν)
    (w ξ : BoundedMultiplier ν) (hinv : ∀ᵐ x ∂ν, w.value x*ξ.value x=1)
    {q : ℝ} (hq : 1 ≤ q) (u v : WeakSobolevJet d m ν S) :
    |coefficientJetForm a u v| ≤ (∑ α, ∑ β, (a α β).bound)*
      WeakSobolevJet.weightedNorm q w u*WeakSobolevJet.weightedNorm q ξ v := by
  rw [coefficientJetForm_apply]
  calc
    _ ≤ ∑ α, ∑ β, |inner ℝ ((a α β).map (jetScalarComponent β u)) (jetScalarComponent α v)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ α, ∑ β, (a α β).bound*WeakSobolevJet.weightedNorm q w u*WeakSobolevJet.weightedNorm q ξ v := by
      apply Finset.sum_le_sum
      intro α _
      apply Finset.sum_le_sum
      intro β _
      rw [← w.inner_inverse ξ hinv]
      have hb : ‖w.map ((a α β).map (jetScalarComponent β u))‖ ≤
          (a α β).bound*WeakSobolevJet.weightedNorm q w u := by
        rw [← w.map_map_comm]
        exact ((a α β).seminorm_le _).trans (mul_le_mul_of_nonneg_left
          (jetScalarComponent_weighted_le hq w u β) (a α β).bound_nonneg)
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hb
        (jetScalarComponent_weighted_le hq ξ v α) (norm_nonneg _) (by positivity [(a α β).bound_nonneg,WeakSobolevJet.weightedNorm_nonneg q w u]))
    _ = _ := by simp only [Finset.sum_mul]


end Carleman
