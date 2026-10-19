module

public import Carleman.Spatial.CartesianKuhnLocalError
public import Carleman.Spatial.WeightedMeasureAnchor

/-! The actual local error for all original H²∩H¹₀ states with a positive
local weight anchor. Its magnitude cancels and only comparability remains. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman

theorem cartesianKuhn_h2_weighted_local_error (d : ℕ) (κ W : ℝ) (hκ : 1 ≤ κ) (hW : 0 < W) :
    ∃ C > 0, ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
      (i : CartesianCellIndex N) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ (σ : BoundedMultiplier (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
        (s : ℝ), 0 < s →
      (∀ᵐ x ∂volume.restrict (cartesianClippedPatch o δ N i), |σ.value x| ≤ W*s ∧ s ≤ W*|σ.value x|) →
      ∀ u : WeakSobolevJet (d+1) 2
        (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
        (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      WeakSobolevJet.value u ∈ dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) →
      let μK := volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
      let e := cartesianKuhnErrorJet o δ hδ N (WeakSobolevJet.truncate (by omega : 1 ≤ 2) u)
      bochnerL2Norm μK (σ.map (WeakSobolevJet.value e))+h*bochnerL2Norm μK (σ.map (WeakSobolevJet.field 1 e)) ≤
        C*h^2*bochnerL2Norm (volume.restrict (cartesianClippedPatch o δ N i)) (σ.map (WeakSobolevJet.field 2 u)) := by
  obtain ⟨A,hA,hlocal⟩ := cartesianKuhn_h2_local_error d κ hκ
  refine ⟨W^2*A,by positivity,?_⟩
  intro o δ hδ N i h hh hlower hupper σ s hs hw u hu
  dsimp only
  let e := cartesianKuhnErrorJet o δ hδ N (WeakSobolevJet.truncate (by omega : 1 ≤ 2) u)
  let μK := volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
  let μB := volume.restrict (cartesianClippedPatch o δ N i)
  have hKB : μK ≤ μB := cartesianClippedPatch_cell_measure o δ hδ N i
  have hBS : μB ≤ volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :=
    Measure.restrict_mono (cartesianClippedPatch_subset_domain o δ N i) le_rfl
  have hwK : ∀ᵐ x ∂μK, |σ.value x| ≤ W*s := (hw.filter_mono (ae_mono hKB)).mono fun _ hx => hx.1
  have hv := σ.bochner_map_le_anchor (hKB.trans hBS) W s hwK (WeakSobolevJet.value e)
  have hg := mul_le_mul_of_nonneg_left
    (σ.bochner_map_le_anchor (hKB.trans hBS) W s hwK (WeakSobolevJet.field 1 e)) hh.le
  have hH := σ.bochner_le_map_anchor hBS W s hs (hw.mono fun _ hx => hx.2) (WeakSobolevJet.field 2 u)
  have he := hlocal o δ hδ N i h hh hlower hupper u hu
  dsimp only at he
  change bochnerL2Norm μK (σ.map (WeakSobolevJet.value e))+
    h*bochnerL2Norm μK (σ.map (WeakSobolevJet.field 1 e)) ≤ _
  calc
    _ ≤ W*s*(bochnerL2Norm μK (WeakSobolevJet.value e)+h*bochnerL2Norm μK (WeakSobolevJet.field 1 e)) :=
      by nlinarith only [hv,hg]
    _ ≤ W*s*(A*h^2*bochnerL2Norm μB (WeakSobolevJet.field 2 u)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ W*s*(A*h^2*((W/s)*bochnerL2Norm μB (σ.map (WeakSobolevJet.field 2 u)))) := by gcongr
    _ = _ := by dsimp only [μB]; field_simp

end Carleman
