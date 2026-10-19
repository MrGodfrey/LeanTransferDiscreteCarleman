module

public import Carleman.Spatial.CartesianKuhnWeightedLocalError
public import Carleman.Spatial.FinitePatchAssembly

/-! Assemble actual cell error bounds using the proven finite Cartesian
cover and clipped-patch multiplicity, including cells on the physical boundary. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhn_error_assembly
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (C h : ℝ) (hC : 0 ≤ C) (hh : 0 ≤ h)
    (σ : BoundedMultiplier (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (e : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
      (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
    (H : Lp (DerivativeFiber d 2) 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (hlocal : ∀ i : CartesianCellIndex N,
      let μK := volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)
      bochnerL2Norm μK (σ.map (WeakSobolevJet.value e))+h*bochnerL2Norm μK (σ.map (WeakSobolevJet.field 1 e)) ≤
        C*h^2*bochnerL2Norm (volume.restrict (cartesianClippedPatch o δ N i)) (σ.map H)) :
    σ.seminorm (WeakSobolevJet.value e)+h*σ.seminorm (WeakSobolevJet.field 1 e) ≤
      Real.sqrt (2*(5^d*d.factorial:ℕ))*C*h^2*σ.seminorm H := by
  let S := openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)
  let M := cartesianKuhnPartition o δ hδ N
  let A : CartesianCellIndex N → Set (SpatialCoordinates d) := fun i => M.cell i ∩ S
  let B := cartesianClippedPatch o δ N
  have hA (i) : MeasurableSet (A i) :=
    (simplicialCell_measurable (M.simplex i).points).inter (openCoordinateBox_isOpen _ _).measurableSet
  have hB (i) : MeasurableSet (B i) := (cartesianClippedPatch_isOpen o δ N i).measurableSet
  have hAS (i) : A i ⊆ S := inter_subset_right
  have hBS (i) : B i ⊆ S := cartesianClippedPatch_subset_domain o δ N i
  have hcover : ∀ᵐ x ∂volume.restrict S, ∃ i, x ∈ A i := by
    filter_upwards [ae_restrict_mem (openCoordinateBox_isOpen _ _).measurableSet] with x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (M.cover hx)
    exact ⟨i,hi,hx⟩
  have hmeasure (i) : volume.restrict (A i)=volume.restrict (M.cell i) := by
    have he := M.cell_restrict_domain (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) i
    rwa [Measure.restrict_restrict (simplicialCell_measurable (M.simplex i).points)] at he
  apply finite_patch_h2_assembly A B hA hB hAS hBS hcover (5^d*d.factorial:ℕ) C h
    (by positivity) hC hh ?_ (σ.map (WeakSobolevJet.value e)) (σ.map (WeakSobolevJet.field 1 e)) (σ.map H) ?_
  · exact Filter.Eventually.of_forall fun x => by
      exact_mod_cast cartesianClippedPatch_multiplicity_le o δ hδ N x
  · intro i
    simp only [subdomainLp_norm_eq_bochner,hmeasure]
    exact hlocal i

end Carleman
