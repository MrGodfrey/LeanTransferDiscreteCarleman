module

public import Carleman.Spatial.CartesianKuhnErrorStability

/-! The actual Q_h has the unweighted local h² value/weak-gradient error
estimate for every original H²∩H¹₀ state, including physical boundary cells. -/
@[expose] public noncomputable section
set_option maxHeartbeats 3200000
open MeasureTheory Set
namespace Carleman

theorem cartesianKuhn_h2_local_error (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
      (i : CartesianCellIndex N) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ u : WeakSobolevJet (d+1) 2
        (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
        (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      WeakSobolevJet.value u ∈ dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) →
      let μK := volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
      let e := cartesianKuhnErrorJet o δ hδ N (WeakSobolevJet.truncate (by omega : 1 ≤ 2) u)
      bochnerL2Norm μK (WeakSobolevJet.value e)+h*bochnerL2Norm μK (WeakSobolevJet.field 1 e) ≤
        C*h^2*bochnerL2Norm (volume.restrict (cartesianClippedPatch o δ N i)) (WeakSobolevJet.field 2 u) := by
  obtain ⟨A,hA,hstab⟩ := cartesianKuhnErrorJet_local_stability (d+1) κ (by linarith)
  obtain ⟨B,hB,hlocal⟩ := cartesianKuhn_h2_local_reproduced_affine d κ hκ
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro o δ hδ N i h hh hlower hupper u hu
  dsimp only
  obtain ⟨p,r,_hp,hrep,hr,he⟩ := hlocal o δ hδ N i h hh hlower hupper u hu
  let S := openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)
  let a := cartesianClippedPatchLower o δ N i
  let b := cartesianClippedPatchUpper o δ N i
  let T := openCoordinateBox a b
  let μK := volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
  let U := WeakSobolevJet.truncate (by omega : 1 ≤ 2) u
  obtain ⟨q,hq⟩ := affineCoefficientPolynomial_surjective p
  let P := affineBoxJet o (fun j => o j+(N j:ℝ)*δ j) q
  have hP : WeakSobolevJet.value P=boundedAffineLp (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j)) p := by
    rw [affineBoxJet_value]
    change boundedAffineLp (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j)) (affineCoefficientPolynomial q)=_
    rw [hq]
  have hPae : WeakSobolevJet.value P =ᵐ[volume.restrict S] p := by
    rw [hP]
    exact boundedAffineLp_ae (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j)) p
  have hKS : μK ≤ volume.restrict S := (cartesianKuhnPartition o δ hδ N).cell_measure_le_domain
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) i
  have hPrep : WeakSobolevJet.value P =ᵐ[μK] cartesianKuhnProjection o δ hδ N (WeakSobolevJet.value P) := by
    rw [hP]
    filter_upwards [(boundedAffineLp_ae (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j)) p).filter_mono
      (ae_mono hKS),ae_restrict_mem (simplicialCell_measurable (cartesianFiniteSimplex o δ hδ N i).points)] with x hx hy
    exact hx.trans (hrep x hy).symm
  have hTS : T ⊆ S := by
    change openCoordinateBox a b ⊆ S
    rw [← cartesianClippedPatch_eq_box]
    exact cartesianClippedPatch_subset_domain o δ N i
  have hTSμ : volume.restrict T ≤ volume.restrict S := Measure.restrict_mono hTS le_rfl
  have hres : WeakSobolevJet.value (U-P) =ᵐ[volume.restrict T] WeakSobolevJet.value r := by
    rw [map_sub]
    filter_upwards [(Lp.coeFn_sub (WeakSobolevJet.value U) (WeakSobolevJet.value P)).filter_mono
      (ae_mono hTSμ),hPae.filter_mono (ae_mono hTSμ),hr] with x h1 h2 h3
    simp only [h1,Pi.sub_apply,h2,h3]
    rfl
  have hjet : WeakSobolevJet.restrictSubdomain hTS (U-P)=r :=
    WeakSobolevJet.restrictSubdomain_eq_of_value_ae hTS (openCoordinateBox_isOpen a b) (U-P) r hres
  have hv : bochnerL2Norm (volume.restrict (cartesianClippedPatch o δ N i)) (WeakSobolevJet.value (U-P))=
      ‖WeakSobolevJet.value r‖ := by
    rw [cartesianClippedPatch_eq_box]
    exact (bochnerL2Norm_congr_ae hres).trans (bochnerL2Norm_coe _)
  have hg : bochnerL2Norm (volume.restrict (cartesianClippedPatch o δ N i)) (WeakSobolevJet.field 1 (U-P))=
      ‖WeakSobolevJet.field 1 r‖ := by
    rw [cartesianClippedPatch_eq_box]
    have hhg : subdomainLp hTS (WeakSobolevJet.field 1 (U-P))=WeakSobolevJet.field 1 r :=
      congrArg (WeakSobolevJet.field 1) hjet
    rw [← hhg,subdomainLp_norm_eq_bochner]
  have hval := cartesianKuhnErrorJet_value_local_invariant o δ hδ N i U P hPrep
  have hfield := cartesianKuhnErrorJet_field_local_invariant o δ hδ N i U P hPrep 1
  change bochnerL2Norm μK (WeakSobolevJet.value (cartesianKuhnErrorJet o δ hδ N U))+
    h*bochnerL2Norm μK (WeakSobolevJet.field 1 (cartesianKuhnErrorJet o δ hδ N U)) ≤ _
  rw [bochnerL2Norm_congr_ae hval,bochnerL2Norm_congr_ae hfield]
  have hs := hstab o δ hδ N i h hh hlower (U-P)
  dsimp only at hs
  rw [hv,hg] at hs
  calc
    _ ≤ A*(‖WeakSobolevJet.value r‖+h*‖WeakSobolevJet.field 1 r‖) := hs
    _ ≤ A*(B*h^2*bochnerL2Norm (volume.restrict (cartesianClippedPatch o δ N i)) (WeakSobolevJet.field 2 u)) :=
      mul_le_mul_of_nonneg_left he hA.le
    _ = _ := by ring

end Carleman
