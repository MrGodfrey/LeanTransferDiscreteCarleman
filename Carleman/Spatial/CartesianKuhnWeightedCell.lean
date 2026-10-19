module

public import Carleman.Spatial.CartesianKuhnWeightedMass
public import Carleman.Spatial.SimplexWeightedStability
public import Carleman.Spatial.CellwiseInverseWeight

/-! Weighted estimates for the actual Cartesian reconstruction and load
on each actual finite cell, using its positive comparison anchor. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhn_weighted_reconstruction_cell_bounds (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ)
    (w : BoundedMultiplier (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (i : CartesianCellIndex N) (W s : ℝ) (hW : 0 < W) (hs : 0 < s)
    (hω : ∀ k, 0 ≤ w.value ((cartesianFiniteSimplex o δ hδ N i).points k))
    (hb : ∀ k, w.value ((cartesianFiniteSimplex o δ hδ N i).points k) ≤ W*s ∧
      s ≤ W*w.value ((cartesianFiniteSimplex o δ hδ N i).points k))
    (hw : ∀ᵐ x ∂volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points),
      |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|) :
    let T := cartesianFiniteSimplex o δ hδ N i
    let E := (volume.real (simplicialCell T.points)/(d+1:ℝ))*
      (∑ k, (w.value (T.points k)*cartesianInteriorData o δ N f (T.points k))^2)
    E ≤ W^4*(d+2:ℝ)*(∫ x in simplicialCell T.points, |w.value x|^2*(cartesianKuhnReconstruction o δ hδ N f x)^2) ∧
    (∫ x in simplicialCell T.points, |w.value x|^2*(cartesianKuhnReconstruction o δ hδ N f x)^2) ≤ W^4*E := by
  dsimp only
  let T := cartesianFiniteSimplex o δ hδ N i
  let c := fun k => cartesianInteriorData o δ N f (T.points k)
  let v := w.restrictMeasure ((cartesianKuhnPartition o δ hδ N).cell_measure_le_domain
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) i)
  have he : (∫ x in simplicialCell T.points, |w.value x|^2*(cartesianKuhnReconstruction o δ hδ N f x)^2)=
      (∫ x in simplicialCell T.points, |w.value x|^2*(simplexNodalInterpolant T c x)^2) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
    rw [cartesianKuhnReconstruction_on_cell o δ hδ N f i hx]
  rw [he]
  have hb' := simplex_weighted_reconstruction_bounds T v c (fun k => w.value (T.points k)) W s hW hs hω hb hw
  simpa only [v,BoundedMultiplier.restrictMeasure,c,T,mul_assoc] using hb'

theorem cartesianKuhn_weighted_load_cell_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ)
    (w : BoundedMultiplier (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (i : CartesianCellIndex N) (W s : ℝ) (hW : 0 < W) (hs : 0 < s)
    (hω : ∀ k, 0 ≤ w.value ((cartesianFiniteSimplex o δ hδ N i).points k))
    (hb : ∀ k, w.value ((cartesianFiniteSimplex o δ hδ N i).points k) ≤ W*s ∧
      s ≤ W*w.value ((cartesianFiniteSimplex o δ hδ N i).points k))
    (hw : ∀ᵐ x ∂volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points),
      |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|) :
    (∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
      |w.value x|^2*(cartesianKuhnLoadLift o δ hδ N f x)^2) ≤
      W^4*(d+2:ℝ)*(volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ))*
      (∑ k, (w.value ((cartesianFiniteSimplex o δ hδ N i).points k)*
        cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))^2) := by
  let T := cartesianFiniteSimplex o δ hδ N i
  let c := cartesianKuhnLoadCoefficients o δ hδ N (cartesianInteriorData o δ N f) i
  let v := w.restrictMeasure ((cartesianKuhnPartition o δ hδ N).cell_measure_le_domain
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) i)
  have he : (∫ x in simplicialCell T.points, |w.value x|^2*(cartesianKuhnLoadLift o δ hδ N f x)^2)=
      (∫ x in simplicialCell T.points, |w.value x|^2*(simplexLoadPolynomial T c x)^2) := by
    apply integral_congr_ae
    filter_upwards [cartesianKuhnLoad_on_cell o δ hδ N (cartesianInteriorData o δ N f) i] with x hx
    change |w.value x|^2*(cartesianKuhnLoad o δ hδ N (cartesianInteriorData o δ N f) x)^2=_
    rw [hx]
  rw [he]
  have h := simplex_weighted_load_bound T v c (fun k => w.value (T.points k)) W s hW hs hω hb hw
  simpa only [v,BoundedMultiplier.restrictMeasure,c,T,cartesianKuhnLoadCoefficients_interiorData] using h

end Carleman
