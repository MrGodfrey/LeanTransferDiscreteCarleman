module

public import Carleman.Spatial.CartesianKuhnErrorLocality

/-! Stability of the genuine value/weak-gradient error on one actual cell,
controlled by the original residual on its actual clipped patch. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem cartesianKuhnErrorJet_local_stability (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C > 0, ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (i : CartesianCellIndex N) (h : ℝ), 0 < h → (∀ j, h/κ ≤ δ j) →
      ∀ u : WeakSobolevJet d 1
        (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
        (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      let μK := volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
      let μB := volume.restrict (cartesianClippedPatch o δ N i)
      bochnerL2Norm μK (WeakSobolevJet.value (cartesianKuhnErrorJet o δ hδ N u))+
        h*bochnerL2Norm μK (WeakSobolevJet.field 1 (cartesianKuhnErrorJet o δ hδ N u)) ≤
      C*(bochnerL2Norm μB (WeakSobolevJet.value u)+h*bochnerL2Norm μB (WeakSobolevJet.field 1 u)) := by
  obtain ⟨A,hA,hgrad⟩ := cartesianKuhnProjection_local_gradient_bound d κ hκ
  refine ⟨A+2,by positivity,?_⟩
  intro o δ hδ N i h hh hlower u
  dsimp only
  let μK := volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
  let μB := volume.restrict (cartesianClippedPatch o δ N i)
  let q := cartesianKuhnProjectionJet o δ hδ N (WeakSobolevJet.value u)
  have hKB : μK ≤ μB := cartesianClippedPatch_cell_measure o δ hδ N i
  have hBS : μB ≤ volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :=
    Measure.restrict_mono (cartesianClippedPatch_subset_domain o δ N i) le_rfl
  have hKS := hKB.trans hBS
  have hv : bochnerL2Norm μK (WeakSobolevJet.value u) ≤ bochnerL2Norm μB (WeakSobolevJet.value u) :=
    bochnerL2Norm_mono_measure ((Lp.memLp _).mono_measure hBS) hKB
  have hg : bochnerL2Norm μK (WeakSobolevJet.field 1 u) ≤ bochnerL2Norm μB (WeakSobolevJet.field 1 u) :=
    bochnerL2Norm_mono_measure ((Lp.memLp _).mono_measure hBS) hKB
  have hq : bochnerL2Norm μK (WeakSobolevJet.value q) ≤ bochnerL2Norm μB (WeakSobolevJet.value u) := by
    rw [bochnerL2Norm_congr_ae ((cartesianKuhnProjectionJet_ae o δ hδ N (WeakSobolevJet.value u)).filter_mono (ae_mono hKS))]
    exact cartesianKuhnProjection_patch_norm_bound o δ hδ N _ i
  have hqg := hgrad o δ hδ N i h hh hlower (WeakSobolevJet.value u)
  change bochnerL2Norm μK (WeakSobolevJet.field 1 q) ≤ (A/h)*bochnerL2Norm μB (WeakSobolevJet.value u) at hqg
  have hev : bochnerL2Norm μK (WeakSobolevJet.value (cartesianKuhnErrorJet o δ hδ N u)) ≤
      2*bochnerL2Norm μB (WeakSobolevJet.value u) := by
    rw [cartesianKuhnErrorJet,map_sub]
    exact (bochnerL2Norm_lp_sub hKS _ _).trans (by linarith)
  have heg : bochnerL2Norm μK (WeakSobolevJet.field 1 (cartesianKuhnErrorJet o δ hδ N u)) ≤
      bochnerL2Norm μB (WeakSobolevJet.field 1 u)+(A/h)*bochnerL2Norm μB (WeakSobolevJet.value u) := by
    rw [cartesianKuhnErrorJet,map_sub]
    exact (bochnerL2Norm_lp_sub hKS _ _).trans (add_le_add hg hqg)
  have hgscaled := mul_le_mul_of_nonneg_left heg hh.le
  have hcancel : h*(A/h)=A := mul_div_cancel₀ A hh.ne'
  have hnn := mul_nonneg hh.le (bochnerL2Norm_nonneg (WeakSobolevJet.field 1 u) (μ := μB))
  change bochnerL2Norm μK (WeakSobolevJet.value (cartesianKuhnErrorJet o δ hδ N u))+
    h*bochnerL2Norm μK (WeakSobolevJet.field 1 (cartesianKuhnErrorJet o δ hδ N u)) ≤ _
  rw [mul_add,← mul_assoc,hcancel] at hgscaled
  nlinarith

end Carleman
