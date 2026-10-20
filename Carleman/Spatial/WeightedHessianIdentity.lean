module
public import Carleman.Geometry.ConvexBoundaryFlux
public import Carleman.Spatial.SmoothDirectionalCalculus
public import Carleman.Spatial.WeakDerivativeStrongLimit
/-! Weighted integration by parts for the actual classical Hessian. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem compact_smooth_product_integrable (f g : SpatialCoordinates d → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) :
    Integrable (fun x => f x*g x) volume :=
  (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_right

theorem integral_smoothD_compact (f g : SpatialCoordinates d → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g)
    (e : SpatialCoordinates d) :
    (∫ x, f x*smoothD e g x) = -(∫ x, smoothD e f x*g x) := by
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (compact_smooth_product_integrable (smoothD e f) g (smoothD_contDiff hf e) (hc.fderiv_apply ℝ e) hg)
    (compact_smooth_product_integrable f (smoothD e g) hf hc (smoothD_contDiff hg e))
    (compact_smooth_product_integrable f g hf hc hg)
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)

theorem weighted_mixed_derivative_pair (η f g : SpatialCoordinates d → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (e v : SpatialCoordinates d) :
    (∫ x, η x*(smoothD e f x*smoothD v g x-smoothD v f x*smoothD e g x)) =
      ∫ x, (smoothD e η x*smoothD v f x-smoothD v η x*smoothD e f x)*g x := by
  let A := fun x => η x*smoothD e f x
  let B := fun x => η x*smoothD v f x
  have hA : ContDiff ℝ ∞ A := hη.mul (smoothD_contDiff hf e)
  have hB : ContDiff ℝ ∞ B := hη.mul (smoothD_contDiff hf v)
  have hcA : HasCompactSupport A := hc.mul_right
  have hcB : HasCompactSupport B := hc.mul_right
  have iA := compact_smooth_product_integrable A (smoothD v g) hA hcA (smoothD_contDiff hg v)
  have iB := compact_smooth_product_integrable B (smoothD e g) hB hcB (smoothD_contDiff hg e)
  have iDA := compact_smooth_product_integrable (smoothD v A) g (smoothD_contDiff hA v) (hcA.fderiv_apply ℝ v) hg
  have iDB := compact_smooth_product_integrable (smoothD e B) g (smoothD_contDiff hB e) (hcB.fderiv_apply ℝ e) hg
  calc
    _ = (∫ x, A x*smoothD v g x)-(∫ x, B x*smoothD e g x) := by
      rw [← integral_sub iA iB]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by dsimp [A,B];ring
    _ = -(∫ x, smoothD v A x*g x)+(∫ x, smoothD e B x*g x) := by
      rw [integral_smoothD_compact A g hA hcA hg,integral_smoothD_compact B g hB hcB hg]
      ring
    _ = _ := by
      rw [← integral_neg,← integral_add (show Integrable (fun x => -(smoothD v A x*g x)) volume from iDA.neg) iDB]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [A,B]
        rw [smoothD_mul hη (smoothD_contDiff hf e),smoothD_mul hη (smoothD_contDiff hf v),smoothD_comm hf e v]
        ring

theorem weighted_hessian_pair (η u : SpatialCoordinates d → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hu : ContDiff ℝ ∞ u)
    (e v : SpatialCoordinates d) :
    (∫ x, η x*(smoothD e (smoothD e u) x*smoothD v (smoothD v u) x-
      (smoothD e (smoothD v u) x)^2)) =
    -(∫ x, smoothD e η x*smoothD e u x*smoothD v (smoothD v u) x-
      smoothD v η x*smoothD e u x*smoothD e (smoothD v u) x) := by
  have hh := weighted_mixed_derivative_pair η (smoothD v u) (smoothD e u)
    hη hc (smoothD_contDiff hu v) (smoothD_contDiff hu e) e v
  calc
    _ = -(∫ x, η x*(smoothD e (smoothD v u) x*smoothD v (smoothD e u) x-
        smoothD v (smoothD v u) x*smoothD e (smoothD e u) x)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by dsimp only;rw [smoothD_comm hu v e];ring
    _ = _ := by
      rw [hh]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring

def smoothHessianSq (u : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, (smoothD (EuclideanSpace.basisFun (Fin d) ℝ i)
    (smoothD (EuclideanSpace.basisFun (Fin d) ℝ j) u) x)^2

theorem smoothHessianSq_contDiff (u : SpatialCoordinates d → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (smoothHessianSq u) :=
  ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (smoothD_contDiff (smoothD_contDiff hu (EuclideanSpace.basisFun (Fin d) ℝ j)) (EuclideanSpace.basisFun (Fin d) ℝ i)).pow 2

theorem levelBoundaryFlux_eq_double_sum (u g : SpatialCoordinates d → ℝ)
    (hu : ContDiff ℝ ∞ u) (x : SpatialCoordinates d) :
    levelBoundaryFlux u g x=∑ i : Fin d, ∑ j : Fin d,
      (smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) u x*
        smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) g x*
        smoothD (EuclideanSpace.basisFun (Fin d) ℝ j) (smoothD (EuclideanSpace.basisFun (Fin d) ℝ j) u) x-
      smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) u x*
        smoothD (EuclideanSpace.basisFun (Fin d) ℝ j) g x*
        smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (smoothD (EuclideanSpace.basisFun (Fin d) ℝ j) u) x) := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hi : inner ℝ (graphSlopeVector u x) (graphSlopeVector g x)=∑ i, smoothD (e i) u x*smoothD (e i) g x := by
    rw [real_inner_comm,graphSlopeVector_inner]
    simp only [graphSlopeVector,map_sum,map_smul,smul_eq_mul,smoothD,e]
  have hH : fderiv ℝ (fderiv ℝ u) x (graphSlopeVector u x) (graphSlopeVector g x)=
      ∑ i, ∑ j, smoothD (e i) u x*smoothD (e j) g x*smoothD (e i) (smoothD (e j) u) x := by
    simp only [graphSlopeVector,map_sum,sum_apply,map_smul,smul_apply,smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change _=fderiv ℝ u x (e i)*fderiv ℝ g x (e j)*fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)
    rw [smooth_directional_fderiv_eq u hu]
    ring
  have hP : spatialLaplacian u x*inner ℝ (graphSlopeVector u x) (graphSlopeVector g x)=
      ∑ i, ∑ j, smoothD (e i) u x*smoothD (e i) g x*smoothD (e j) (smoothD (e j) u) x := by
    rw [hi,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [spatialLaplacian,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change smoothD (e j) (smoothD (e j) u) x*(smoothD (e i) u x*smoothD (e i) g x)=_
    ring
  rw [levelBoundaryFlux,hP,hH]
  simp only [Finset.sum_sub_distrib,e]

theorem weighted_hessian_identity (η u : SpatialCoordinates d → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hu : ContDiff ℝ ∞ u) :
    (∫ x, η x*((spatialLaplacian u x)^2-smoothHessianSq u x)) =
      -(∫ x, ∑ i : Fin d, ∑ j : Fin d,
        (smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) η x*
          smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) u x*
          smoothD (EuclideanSpace.basisFun (Fin d) ℝ j) (smoothD (EuclideanSpace.basisFun (Fin d) ℝ j) u) x-
        smoothD (EuclideanSpace.basisFun (Fin d) ℝ j) η x*
          smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) u x*
          smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (smoothD (EuclideanSpace.basisFun (Fin d) ℝ j) u) x)) := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  let L := fun (i j : Fin d) x => η x*(smoothD (e i) (smoothD (e i) u) x*
    smoothD (e j) (smoothD (e j) u) x-(smoothD (e i) (smoothD (e j) u) x)^2)
  let R := fun (i j : Fin d) x => smoothD (e i) η x*smoothD (e i) u x*smoothD (e j) (smoothD (e j) u) x-
    smoothD (e j) η x*smoothD (e i) u x*smoothD (e i) (smoothD (e j) u) x
  have hL (i j : Fin d) : Integrable (L i j) volume :=
    compact_smooth_product_integrable η _ hη hc
      (((smoothD_contDiff (smoothD_contDiff hu _) _).mul (smoothD_contDiff (smoothD_contDiff hu _) _)).sub
        ((smoothD_contDiff (smoothD_contDiff hu _) _).pow 2))
  have hR (i j : Fin d) : Integrable (R i j) volume := by
    have ha := compact_smooth_product_integrable (smoothD (e i) η)
      (fun x => smoothD (e i) u x*smoothD (e j) (smoothD (e j) u) x)
      (smoothD_contDiff hη _) (hc.fderiv_apply ℝ _) ((smoothD_contDiff hu _).mul (smoothD_contDiff (smoothD_contDiff hu _) _))
    have hb := compact_smooth_product_integrable (smoothD (e j) η)
      (fun x => smoothD (e i) u x*smoothD (e i) (smoothD (e j) u) x)
      (smoothD_contDiff hη _) (hc.fderiv_apply ℝ _) ((smoothD_contDiff hu _).mul (smoothD_contDiff (smoothD_contDiff hu _) _))
    simpa only [R,Pi.sub_def,mul_assoc] using ha.sub hb
  have he (x : SpatialCoordinates d) : η x*((spatialLaplacian u x)^2-smoothHessianSq u x)=∑ i, ∑ j, L i j x := by
    change η x*((∑ i, smoothD (e i) (smoothD (e i) u) x)^2-
      ∑ i, ∑ j, (smoothD (e i) (smoothD (e j) u) x)^2)=_
    simp only [L,pow_two,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    _ = ∫ x, ∑ i, ∑ j, L i j x := integral_congr_ae (Filter.Eventually.of_forall he)
    _ = ∑ i, ∑ j, ∫ x, L i j x := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hL i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hL i j)
    _ = ∑ i, ∑ j, -(∫ x, R i j x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact weighted_hessian_pair η u hη hc hu (e i) (e j)
    _ = -(∫ x, ∑ i, ∑ j, R i j x) := by
      simp only [Finset.sum_neg_distrib]
      congr 1
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hR i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hR i j)).symm
    _ = _ := rfl

theorem weighted_level_hessian_identity (η u g κ : SpatialCoordinates d → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hu : ContDiff ℝ ∞ u)
    (hchain : ∀ x, fderiv ℝ η x=(-κ x) • fderiv ℝ g x) :
    (∫ x, η x*((spatialLaplacian u x)^2-smoothHessianSq u x)) =
      ∫ x, κ x*levelBoundaryFlux u g x := by
  rw [weighted_hessian_identity η u hη hc hu,← integral_neg]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp only
  rw [levelBoundaryFlux_eq_double_sum u g hu,Finset.mul_sum]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smoothD,hchain,smul_apply,smul_eq_mul]
  ring

theorem weighted_laplacian_identity (η g : SpatialCoordinates d → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hg : ContDiff ℝ ∞ g) :
    (∫ x, η x*spatialLaplacian g x)=
      -(∫ x, ∑ i : Fin d, smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) η x*
        smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) g x) := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hL (i : Fin d) : Integrable (fun x => η x*smoothD (e i) (smoothD (e i) g) x) volume :=
    compact_smooth_product_integrable η _ hη hc (smoothD_contDiff (smoothD_contDiff hg _) _)
  have hR (i : Fin d) : Integrable (fun x => smoothD (e i) η x*smoothD (e i) g x) volume :=
    compact_smooth_product_integrable _ _ (smoothD_contDiff hη _) (hc.fderiv_apply ℝ _) (smoothD_contDiff hg _)
  calc
    _ = ∫ x, ∑ i, η x*smoothD (e i) (smoothD (e i) g) x := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun x => ?_
      change η x*(∑ i, smoothD (e i) (smoothD (e i) g) x)=_
      exact Finset.mul_sum _ _ _
    _ = ∑ i, ∫ x, η x*smoothD (e i) (smoothD (e i) g) x := integral_finsetSum _ (fun i _ => hL i)
    _ = ∑ i, -(∫ x, smoothD (e i) η x*smoothD (e i) g x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_smoothD_compact η (smoothD (e i) g) hη hc (smoothD_contDiff hg _) _
    _ = _ := by
      rw [Finset.sum_neg_distrib]
      congr 1
      exact (integral_finsetSum _ (fun i _ => hR i)).symm

theorem weighted_level_gradient_mass (η g κ : SpatialCoordinates d → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hg : ContDiff ℝ ∞ g)
    (hchain : ∀ x, fderiv ℝ η x=(-κ x) • fderiv ℝ g x) :
    (∫ x, κ x*‖graphSlopeVector g x‖^2) = ∫ x, η x*spatialLaplacian g x := by
  rw [weighted_laplacian_identity η g hη hc hg,← integral_neg]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp only
  rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [graphSlopeVector_apply,smoothD,hchain,smul_apply,smul_eq_mul]
  ring

end Carleman
