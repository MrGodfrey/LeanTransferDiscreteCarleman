module

public import Carleman.Geometry.CartesianDualCells
public import Carleman.Spatial.FiniteCellReconstruction
public import Carleman.Spatial.CartesianPhysicalControlIsometry

/-! The manuscript's E_h and K_h: actual dual-cell reconstruction and averaging of full physical data. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

def cartesianCellIsometry (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) :
    CartesianPhysicalState δ hδ N →ₗᵢ[ℝ]
      Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  finiteCellIsometry (cartesianDualCell o δ N) (cartesianDualCell_measurable o δ N)
    (Finset.prod_pos (fun j _ => hδ j)) (cartesianDualCell_disjoint o δ hδ N)
    (cartesianDualCell_restrict_volume o δ hδ N)

theorem cartesianCellIsometry_ae (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (z : CartesianPhysicalState δ hδ N) :
    cartesianCellIsometry o δ hδ N z =ᵐ[volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))]
      fun x => ∑ a, (cartesianDualCell o δ N a).indicator (fun _ => z a) x :=
  finiteCellLinear_ae _ _ _ z

theorem cartesianCellIsometry_inner (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (z w : CartesianPhysicalState δ hδ N) :
    inner ℝ (cartesianCellIsometry o δ hδ N z) (cartesianCellIsometry o δ hδ N w)=inner ℝ z w :=
  (cartesianCellIsometry o δ hδ N).inner_map_map z w

def cartesianCellControl (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) : CartesianPhysicalControl o δ hδ N ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  (cartesianCellIsometry o δ hδ N).toContinuousLinearMap.comp
    (cartesianPhysicalControlExtension o δ hδ N ω)

theorem cartesianCellControl_norm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (u : CartesianPhysicalControl o δ hδ N ω) :
    ‖cartesianCellControl o δ hδ N ω u‖=‖u‖ := by
  change ‖cartesianCellIsometry o δ hδ N (cartesianPhysicalControlExtension o δ hδ N ω u)‖=_
  rw [LinearIsometry.norm_map,cartesianPhysicalControlExtension_norm]

theorem cartesianCellControl_pairing (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (u : CartesianPhysicalControl o δ hδ N ω)
    (z : CartesianPhysicalState δ hδ N) :
    inner ℝ (cartesianCellControl o δ hδ N ω u) (cartesianCellIsometry o δ hδ N z)=
      inner ℝ u ((cartesianPhysicalControlExtension o δ hδ N ω).adjoint z) := by
  change inner ℝ (cartesianCellIsometry o δ hδ N (cartesianPhysicalControlExtension o δ hδ N ω u))
    (cartesianCellIsometry o δ hδ N z)=_
  rw [LinearIsometry.inner_map_map,ContinuousLinearMap.adjoint_inner_right]

theorem cartesianCellIsometry_adjoint_average (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (a : CartesianInteriorIndex N) :
    ((cartesianCellIsometry o δ hδ N).toContinuousLinearMap.adjoint f) a=
      (∏ j, δ j)⁻¹*(∫ x in cartesianDualCell o δ N a, f x ∂volume) := by
  have hh := finiteCellIsometry_adjoint (cartesianDualCell o δ N)
    (cartesianDualCell_measurable o δ N) (Finset.prod_pos (fun j _ => hδ j))
    (cartesianDualCell_disjoint o δ hδ N) (cartesianDualCell_restrict_volume o δ hδ N) f a
  rw [Measure.restrict_restrict (cartesianDualCell_measurable o δ N a),
    Set.inter_eq_left.mpr (cartesianDualCell_subset o δ hδ N a)] at hh
  exact hh

theorem cartesianCellIsometry_average_norm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    ‖(cartesianCellIsometry o δ hδ N).toContinuousLinearMap.adjoint f‖ ≤ ‖f‖ :=
  finiteCellIsometry_average_norm _ _ _ _ _ f

end Carleman
