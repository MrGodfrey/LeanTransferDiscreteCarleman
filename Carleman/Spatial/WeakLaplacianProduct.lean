module

public import Carleman.Spatial.WeakProductComponents
public import Carleman.Spatial.DirichletWeakProduct

/-! The negative Laplacian product rule directly in the genuine
weak H¹ graph, without assuming H² elliptic regularity. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem weakGradientPairing_product_test (hS : IsOpen S)
    (w : BoundedMultiplier (volume.restrict S))
    (dw ddw : Fin d → BoundedMultiplier (volume.restrict S))
    (hw : ContDiffOn ℝ ∞ w.value S) (hd : ∀ i, ContDiffOn ℝ ∞ (dw i).value S)
    (hdw : ∀ i, (dw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (hddw : ∀ i, (ddw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ (dw i).value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (φ : SpatialTest S) :
    weakGradientPairing (weakFirstProduct hS (ae_restrict_mem hS.measurableSet) w dw hw hdw u) φ.sobolevJet =
      weakGradientPairing u (φ.mulOn hS hw).sobolevJet-
        ∑ i : Fin d, inner ℝ
          ((2:ℝ) • (dw i).map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))+
            (ddw i).map (WeakSobolevJet.value u)) (φ.toLp (volume.restrict S)) := by
  rw [weakGradientPairing_coordinates,weakGradientPairing_coordinates,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [weakFirstProduct_component,φ.sobolevJet_derivative,(φ.mulOn hS hw).sobolevJet_derivative,
    φ.mulOn_derivativeLp hS (ae_restrict_mem hS.measurableSet) _ w (dw i) hw (hdw i)]
  have hb := weak_product_coordinate_test hS u φ i (dw i) (ddw i) (hd i) (hddw i)
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,w.inner_map_left,(dw i).inner_map_left] at hb ⊢
  linarith only [hb]

theorem IsWeakNegativeLaplacian.mul (hS : IsOpen S)
    (w : BoundedMultiplier (volume.restrict S))
    (dw ddw : Fin d → BoundedMultiplier (volume.restrict S))
    (hw : ContDiffOn ℝ ∞ w.value S) (hd : ∀ i, ContDiffOn ℝ ∞ (dw i).value S)
    (hdw : ∀ i, (dw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (hddw : ∀ i, (ddw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ (dw i).value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (f : Lp ℝ 2 (volume.restrict S))
    (hu : IsWeakNegativeLaplacian u f) :
    IsWeakNegativeLaplacian
      (weakFirstProduct hS (ae_restrict_mem hS.measurableSet) w dw hw hdw u)
      (w.map f-∑ i : Fin d,
        ((2:ℝ) • (dw i).map (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))+
          (ddw i).map (WeakSobolevJet.value u))) := by
  intro φ
  rw [weakGradientPairing_product_test hS w dw ddw hw hd hdw hddw,hu,
    SpatialTest.mulOn_toLp,inner_sub_left,sum_inner,w.inner_map_left]

end Carleman
