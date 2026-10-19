module

public import Carleman.Geometry.CartesianClippedPatch
public import Carleman.Spatial.CartesianKuhnProjection

/-! The original Q_h acts only on a concrete clipped rectangular patch,
and its local L² bound holds for every original L² state. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnHat_support_subset_clippedPatch (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) (a : CartesianInteriorIndex N)
    (ha : cartesianInteriorPoint o δ N a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points) :
    Function.support (cartesianKuhnHat o δ hδ N (cartesianInteriorLatticeIndex N a)) ⊆
      cartesianClippedPatch o δ N i := by
  intro x hx
  constructor
  · by_contra hn
    exact hx (cartesianKuhnHat_zero_compl o δ hδ N _ (cartesianInteriorPoint_mem o δ hδ N a) hn)
  · exact cartesianKuhnStarPatch_subset_patch o δ hδ _ _
      (cartesianKuhnHat_tsupport_subset_cellStar o δ hδ N _ i ha (subset_closure hx))

theorem cartesianKuhnProjection_patch_sq_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (i : CartesianCellIndex N) :
    (∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
      (cartesianKuhnProjection o δ hδ N u x)^2) ≤ ∫ x in cartesianClippedPatch o δ N i, (u x)^2 :=
  cartesianKuhnProjection_local_sq_bound o δ hδ N u i _
    (cartesianClippedPatch_subset_domain o δ N i) (fun a => cartesianKuhnHat_support_subset_clippedPatch o δ hδ N i a)

theorem cartesianKuhnProjection_patch_norm_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (i : CartesianCellIndex N) :
    bochnerL2Norm (volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points))
      (cartesianKuhnProjection o δ hδ N u) ≤
        bochnerL2Norm (volume.restrict (cartesianClippedPatch o δ N i)) u :=
  cartesianKuhnProjection_local_norm_bound o δ hδ N u i _
    (cartesianClippedPatch_subset_domain o δ N i) (fun a => cartesianKuhnHat_support_subset_clippedPatch o δ hδ N i a)

theorem cartesianKuhnProjection_patch_congr (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (i : CartesianCellIndex N) (he : u =ᵐ[volume.restrict (cartesianClippedPatch o δ N i)] v)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
    cartesianKuhnProjection o δ hδ N u x=cartesianKuhnProjection o δ hδ N v x :=
  cartesianKuhnProjection_local_congr o δ hδ N u v i _
    (cartesianClippedPatch_subset_domain o δ N i) (fun a => cartesianKuhnHat_support_subset_clippedPatch o δ hδ N i a) he hx

end Carleman
