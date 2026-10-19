module

public import Carleman.Spatial.CoordinateBoxTraceLinearMap

/-! Continuity of the actual weak face trace in the original complete H¹
graph topology, proved from the genuine physical trace inequality. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem weakJetBoxFace_bounded (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (upper : Bool) : ∃ C > 0, ∀ u : WeakSobolevJet (d+1) 1
      (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b),
      ‖weakJetBoxFaceLinearMap i a b hi upper u‖ ≤ C*‖u‖ := by
  let V : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b))
      (openCoordinateBox a b) →L[ℝ] Lp ℝ 2 (volume.restrict (openCoordinateBox a b)) :=
    WeakSobolevJet.valueCLM
  let B : ℝ := 2/(b i-a i)*‖V‖^2+2*(b i-a i)
  have hL : 0 < b i-a i := sub_pos.mpr hi
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B+1,by positivity,?_⟩
  intro u
  have hv : ‖WeakSobolevJet.value u‖ ≤ ‖V‖*‖u‖ := V.le_opNorm u
  have hg := WeakSobolevJet.norm_field_le (1 : Fin 2) u
  have ht := weakJetBoxFaceTrace_norm_sq i a b hi upper u
  change ‖weakJetBoxFaceLinearMap i a b hi upper u‖^2 ≤ _ at ht
  have hv2 := mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hv) (by positivity : 0 ≤ 2/(b i-a i))
  have hg2 := mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hg) (by positivity : 0 ≤ 2*(b i-a i))
  have hbnd : ‖weakJetBoxFaceLinearMap i a b hi upper u‖^2 ≤ B*‖u‖^2 := by
    exact ht.trans ((add_le_add hv2 hg2).trans_eq (by dsimp only [B]; ring))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hb : B ≤ (B+1)^2 := by nlinarith [sq_nonneg B]
  exact hbnd.trans ((mul_le_mul_of_nonneg_right hb (sq_nonneg ‖u‖)).trans_eq (by ring))

def weakJetBoxFaceCLM (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) (upper : Bool) :
    WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b) →L[ℝ]
      Lp ℝ 2 (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))) :=
  (weakJetBoxFaceLinearMap i a b hi upper).mkContinuous
    (weakJetBoxFace_bounded i a b hi upper).choose
    (weakJetBoxFace_bounded i a b hi upper).choose_spec.2

theorem weakJetBoxFaceCLM_apply (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool)
    (u : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)) :
    weakJetBoxFaceCLM i a b hi upper u=weakJetBoxFaceLinearMap i a b hi upper u := rfl

end Carleman
