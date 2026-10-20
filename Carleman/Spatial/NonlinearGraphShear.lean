module
public import Carleman.Spatial.VariableCoefficientNormalRecovery
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
/-! Actual nonlinear graph shears and their volume change. The height
function is smooth and invariant along the chosen normal coordinate.
The shear and its actual inverse map the half-space onto its epigraph;
the Jacobian determinant is proved to equal one, so the actual restricted
volume and L² classes are transported without a missing density. Smooth
tests and the true slope multipliers supply later weak chain rules. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

def spatialGraphShear (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : Continuous ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    SpatialCoordinates d ≃ₜ SpatialCoordinates d where
  toFun x := x+ψ x • EuclideanSpace.basisFun (Fin d) ℝ r
  invFun x := x-ψ x • EuclideanSpace.basisFun (Fin d) ℝ r
  left_inv x := by simp only [htrans]; abel
  right_inv x := by
    dsimp only
    have ht := htrans x (-ψ x)
    rw [neg_smul,← sub_eq_add_neg] at ht
    rw [ht]
    abel
  continuous_toFun := continuous_id.add (hψ.smul continuous_const)
  continuous_invFun := continuous_id.sub (hψ.smul continuous_const)

theorem spatialGraphShear_psi (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : Continuous ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) (x : SpatialCoordinates d) :
    ψ (spatialGraphShear r ψ hψ htrans x)=ψ x := htrans x (ψ x)

theorem spatialGraphShear_halfspace (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : Continuous ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    spatialGraphShear r ψ hψ htrans ⁻¹' {x | ψ x < x r} = {x | 0 < x r} := by
  ext x
  change ψ (spatialGraphShear r ψ hψ htrans x) < (x+ψ x • EuclideanSpace.basisFun (Fin d) ℝ r) r ↔ _
  rw [spatialGraphShear_psi r ψ hψ htrans x]
  simp only [PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
  change ψ x < x r+ψ x ↔ 0 < x r
  constructor <;> intro h <;> linarith

theorem spatialGraphShear_hasFDerivAt (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) (x : SpatialCoordinates d) :
    HasFDerivAt (spatialGraphShear r ψ hψ.continuous htrans)
      ((ContinuousLinearMap.id ℝ (SpatialCoordinates d))+
        (fderiv ℝ ψ x).smulRight (EuclideanSpace.basisFun (Fin d) ℝ r)) x :=
  (hasFDerivAt_id x).add ((hψ.differentiable (by simp) x).hasFDerivAt.smul_const _)

theorem spatialGraphShear_normal_derivative (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) (x : SpatialCoordinates d) :
    fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ r)=0 := by
  have hl : HasDerivAt (fun t : ℝ => x+t • EuclideanSpace.basisFun (Fin d) ℝ r)
      (EuclideanSpace.basisFun (Fin d) ℝ r) 0 :=
    by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.basisFun (Fin d) ℝ r)).const_add x
  have hp : HasFDerivAt ψ (fderiv ℝ ψ x) (x+(0 : ℝ) • EuclideanSpace.basisFun (Fin d) ℝ r) := by
    simpa using (hψ.differentiable (by simp) x).hasFDerivAt
  have hd := hp.comp_hasDerivAt (0 : ℝ) hl
  have he : (fun t : ℝ => ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r))=fun _ => ψ x := funext (htrans x)
  change HasDerivAt (fun t : ℝ => ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)) _ 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 (ψ x))

theorem spatialGraphShear_det (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) (x : SpatialCoordinates d) :
    (fderiv ℝ (spatialGraphShear r ψ hψ.continuous htrans) x).det=1 := by
  classical
  rw [(spatialGraphShear_hasFDerivAt r ψ hψ htrans x).fderiv]
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let v : Fin d → ℝ := fun j => fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ j)
  let e : Fin d → ℝ := fun i => if i=r then 1 else 0
  have hm : LinearMap.toMatrix b b
      ((ContinuousLinearMap.id ℝ (SpatialCoordinates d))+
        (fderiv ℝ ψ x).smulRight (EuclideanSpace.basisFun (Fin d) ℝ r)).toLinearMap =
      1+Matrix.replicateCol Unit e * Matrix.replicateRow Unit v := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp [b,v,e,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,
      Matrix.mul_apply,Matrix.one_apply]
  change LinearMap.det (((ContinuousLinearMap.id ℝ (SpatialCoordinates d))+
    (fderiv ℝ ψ x).smulRight (EuclideanSpace.basisFun (Fin d) ℝ r)).toLinearMap) = 1
  rw [← LinearMap.det_toMatrix b,hm,Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hz := spatialGraphShear_normal_derivative r ψ hψ htrans x
  simpa [dotProduct,e,v] using hz

theorem spatialGraphShear_measurePreserving (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    MeasurePreserving (spatialGraphShear r ψ hψ.continuous htrans) volume volume := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  refine ⟨F.continuous.measurable,?_⟩
  have hdiff (x) (_hx : x ∈ (univ : Set (SpatialCoordinates d))) :
      HasFDerivWithinAt F (fderiv ℝ F x) univ x :=
    (spatialGraphShear_hasFDerivAt r ψ hψ htrans x).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have he := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (SpatialCoordinates d))
    MeasurableSet.univ.nullMeasurableSet hdiff F.injective.injOn
  have hdensity : (fun x => ENNReal.ofReal |(fderiv ℝ F x).det|)=(1 : SpatialCoordinates d → ENNReal) := by
    funext x
    rw [spatialGraphShear_det r ψ hψ htrans x]
    simp
  rw [hdensity,withDensity_one] at he
  simpa only [Measure.restrict_univ,Set.image_univ,F.surjective.range_eq] using he

theorem spatialGraphShear_measurePreserving_restrict (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (T : Set (SpatialCoordinates d)) :
    MeasurePreserving (spatialGraphShear r ψ hψ.continuous htrans)
      (volume.restrict ((spatialGraphShear r ψ hψ.continuous htrans) ⁻¹' T)) (volume.restrict T) := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  refine ⟨F.continuous.measurable,?_⟩
  have he := F.toMeasurableEquiv.measurableEmbedding.restrict_map volume T
  change (Measure.map (spatialGraphShear r ψ hψ.continuous htrans) volume).restrict T = _ at he
  rw [(spatialGraphShear_measurePreserving r ψ hψ htrans).map_eq] at he
  exact he.symm

theorem spatialGraphShear_halfspace_measurePreserving (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    MeasurePreserving (spatialGraphShear r ψ hψ.continuous htrans)
      (volume.restrict {x : SpatialCoordinates d | 0 < x r}) (volume.restrict {x | ψ x < x r}) := by
  simpa only [spatialGraphShear_halfspace] using
    spatialGraphShear_measurePreserving_restrict r ψ hψ htrans {x | ψ x < x r}

theorem spatialGraphShear_contDiff (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    ContDiff ℝ ∞ (spatialGraphShear r ψ hψ.continuous htrans) :=
  contDiff_id.add (hψ.smul contDiff_const)

theorem spatialGraphShear_symm_contDiff (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    ContDiff ℝ ∞ (spatialGraphShear r ψ hψ.continuous htrans).symm :=
  contDiff_id.sub (hψ.smul contDiff_const)

theorem spatialGraphShear_fderiv_invariant (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (x : SpatialCoordinates d) (t : ℝ) :
    fderiv ℝ ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=fderiv ℝ ψ x := by
  have hd := (hψ.differentiable (by simp) (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const (t • EuclideanSpace.basisFun (Fin d) ℝ r))
  have he : (ψ ∘ (fun y => y+t • EuclideanSpace.basisFun (Fin d) ℝ r))=ψ := funext fun y => htrans y t
  simp only [id_eq] at hd
  rw [he] at hd
  simpa only [ContinuousLinearMap.comp_id] using hd.fderiv.symm

namespace SpatialTest
variable {S T : Set (SpatialCoordinates d)}

def pullbackSmoothHomeomorph (φ : SpatialTest T) (F : SpatialCoordinates d ≃ₜ SpatialCoordinates d)
    (hF : ContDiff ℝ ∞ F) (hST : F ⁻¹' T ⊆ S) : SpatialTest S where
  value := φ.value ∘ F
  smooth := φ.smooth.comp hF
  compact := φ.compact.comp_homeomorph F
  support := by
    rw [tsupport_comp_eq_preimage]
    exact (preimage_mono φ.support).trans hST

theorem pullbackSmoothHomeomorph_derivative (φ : SpatialTest T) (F : SpatialCoordinates d ≃ₜ SpatialCoordinates d)
    (hF : ContDiff ℝ ∞ F) (hST : F ⁻¹' T ⊆ S) (x e : SpatialCoordinates d) :
    fderiv ℝ (φ.pullbackSmoothHomeomorph F hF hST).value x e =
      fderiv ℝ φ.value (F x) (fderiv ℝ F x e) := by
  have hd := (φ.smooth.differentiable (by simp) (F x)).hasFDerivAt.comp x
    (hF.differentiable (by simp) x).hasFDerivAt
  exact congrArg (fun L : SpatialCoordinates d →L[ℝ] ℝ => L e) hd.fderiv

theorem pullbackGraphShear_derivative (φ : SpatialTest T) (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (hST : spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T ⊆ S) (x e : SpatialCoordinates d) :
    fderiv ℝ (φ.pullbackSmoothHomeomorph (spatialGraphShear r ψ hψ.continuous htrans)
      (spatialGraphShear_contDiff r ψ hψ htrans) hST).value x e =
      fderiv ℝ φ.value (spatialGraphShear r ψ hψ.continuous htrans x) e+
        fderiv ℝ ψ x e * fderiv ℝ φ.value (spatialGraphShear r ψ hψ.continuous htrans x)
          (EuclideanSpace.basisFun (Fin d) ℝ r) := by
  rw [pullbackSmoothHomeomorph_derivative,(spatialGraphShear_hasFDerivAt r ψ hψ htrans x).fderiv]
  simp only [add_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
    map_add,map_smul,smul_eq_mul]

end SpatialTest

theorem SpatialTest.pullbackGraphShear_symm_derivative {S T : Set (SpatialCoordinates d)}
    (φ : SpatialTest T) (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (hST : (spatialGraphShear r ψ hψ.continuous htrans).symm ⁻¹' T ⊆ S) (x e : SpatialCoordinates d) :
    fderiv ℝ (φ.pullbackSmoothHomeomorph (spatialGraphShear r ψ hψ.continuous htrans).symm
      (spatialGraphShear_symm_contDiff r ψ hψ htrans) hST).value x e =
      fderiv ℝ φ.value ((spatialGraphShear r ψ hψ.continuous htrans).symm x) e-
        fderiv ℝ ψ x e * fderiv ℝ φ.value ((spatialGraphShear r ψ hψ.continuous htrans).symm x)
          (EuclideanSpace.basisFun (Fin d) ℝ r) := by
  have hd : HasFDerivAt (spatialGraphShear r ψ hψ.continuous htrans).symm
      ((ContinuousLinearMap.id ℝ (SpatialCoordinates d))-
        (fderiv ℝ ψ x).smulRight (EuclideanSpace.basisFun (Fin d) ℝ r)) x :=
    (hasFDerivAt_id x).sub ((hψ.differentiable (by simp) x).hasFDerivAt.smul_const _)
  rw [pullbackSmoothHomeomorph_derivative,hd.fderiv]
  simp only [sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
    map_sub,map_smul,smul_eq_mul]

def graphSlopeMultiplier (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ) (j : Fin d) :
    BoundedMultiplier (volume : Measure (SpatialCoordinates d)) where
  value x := fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ j)
  measurable := ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
  bound := C
  bound_nonneg := C.coe_nonneg
  bounded := Eventually.of_forall fun x => by
    have hb := (fderiv ℝ ψ x).le_opNorm (EuclideanSpace.basisFun (Fin d) ℝ j)
    rw [Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one j,mul_one] at hb
    exact hb.trans (norm_fderiv_le_of_lipschitz ℝ hC)

theorem graphSlopeMultiplier_contDiff (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ) (j : Fin d) :
    ContDiff ℝ ∞ (graphSlopeMultiplier ψ hψ hC j).value :=
  (contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const

theorem graphSlopeMultiplier_normal_derivative (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (j : Fin d) (x : SpatialCoordinates d) :
    fderiv ℝ (graphSlopeMultiplier ψ hψ hC j).value x (EuclideanSpace.basisFun (Fin d) ℝ r)=0 := by
  apply spatialGraphShear_normal_derivative r _ (graphSlopeMultiplier_contDiff ψ hψ hC j) _ x
  intro y t
  exact congrArg (fun L : SpatialCoordinates d →L[ℝ] ℝ => L (EuclideanSpace.basisFun (Fin d) ℝ j))
    (spatialGraphShear_fderiv_invariant r ψ hψ htrans y t)

def homeomorphPullbackLp {ν μ : Measure (SpatialCoordinates d)}
    (F : SpatialCoordinates d ≃ₜ SpatialCoordinates d) (hm : MeasurePreserving F μ ν) :
    Lp ℝ 2 ν →ₗᵢ[ℝ] Lp ℝ 2 μ := Lp.compMeasurePreservingₗᵢ ℝ F hm

theorem homeomorphPullbackLp_ae {ν μ : Measure (SpatialCoordinates d)}
    (F : SpatialCoordinates d ≃ₜ SpatialCoordinates d) (hm : MeasurePreserving F μ ν) (u : Lp ℝ 2 ν) :
    homeomorphPullbackLp F hm u =ᵐ[μ] u ∘ F := Lp.coeFn_compMeasurePreserving _ _

theorem homeomorphPullbackLp_inverse {ν μ : Measure (SpatialCoordinates d)}
    (F : SpatialCoordinates d ≃ₜ SpatialCoordinates d) (hm : MeasurePreserving F μ ν) (u : Lp ℝ 2 ν) :
    homeomorphPullbackLp F.symm (hm.symm F.toMeasurableEquiv) (homeomorphPullbackLp F hm u)=u := by
  apply Lp.ext
  filter_upwards [homeomorphPullbackLp_ae F.symm (hm.symm F.toMeasurableEquiv) (homeomorphPullbackLp F hm u),
    (hm.symm F.toMeasurableEquiv).quasiMeasurePreserving.ae (homeomorphPullbackLp_ae F hm u)] with y hy hx
  simpa using hy.trans hx

theorem integral_mul_homeomorphPullbackLp {ν μ : Measure (SpatialCoordinates d)}
    (F : SpatialCoordinates d ≃ₜ SpatialCoordinates d) (hm : MeasurePreserving F μ ν)
    (u : Lp ℝ 2 ν) (a : SpatialCoordinates d → ℝ) :
    (∫ x, a x*homeomorphPullbackLp F hm u x ∂μ)=∫ y, a (F.symm y)*u y ∂ν := by
  calc
    _ = ∫ x, a x*u (F x) ∂μ := integral_congr_ae ((homeomorphPullbackLp_ae F hm u).mono fun x hx => by rw [hx]; rfl)
    _ = _ := by simpa using hm.integral_comp' (f := F.toMeasurableEquiv) (fun y => a (F.symm y)*u y)

theorem SpatialTest.pullbackSmoothHomeomorph_toLp {ν μ : Measure (SpatialCoordinates d)}
    [IsFiniteMeasureOnCompacts ν] [IsFiniteMeasureOnCompacts μ] {S T : Set (SpatialCoordinates d)}
    (φ : SpatialTest T) (F : SpatialCoordinates d ≃ₜ SpatialCoordinates d)
    (hF : ContDiff ℝ ∞ F) (hST : F ⁻¹' T ⊆ S) (hm : MeasurePreserving F μ ν) :
    (φ.pullbackSmoothHomeomorph F hF hST).toLp μ = homeomorphPullbackLp F hm (φ.toLp ν) := by
  apply Lp.ext
  filter_upwards [(φ.pullbackSmoothHomeomorph F hF hST).toLp_ae μ,
    homeomorphPullbackLp_ae F hm (φ.toLp ν),hm.quasiMeasurePreserving.ae (φ.toLp_ae ν)] with x hx hy hz
  rw [hx,hy]
  exact hz.symm

end Carleman
