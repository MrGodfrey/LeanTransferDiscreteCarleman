module
public import Carleman.Spatial.GraphShearHessianTransport
/-! Actual graph metric, its quantitative ellipticity and coefficient regularity,
and transformation of the original full weak Poisson equation. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

def graphCovectorMap (r : Fin d) (b : SpatialCoordinates d) : SpatialCoordinates d →L[ℝ] SpatialCoordinates d :=
  ContinuousLinearMap.id ℝ _-(EuclideanSpace.proj r).smulRight b

theorem graphCovectorMap_apply (r : Fin d) (b ξ : SpatialCoordinates d) :
    graphCovectorMap r b ξ=ξ-(ξ r) • b := rfl

theorem graphCovectorMap_inverse (r : Fin d) (b : SpatialCoordinates d) (hb : b r=0) (ξ : SpatialCoordinates d) :
    graphCovectorMap r (-b) (graphCovectorMap r b ξ)=ξ := by
  simp only [graphCovectorMap_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,hb,mul_zero,sub_zero,smul_neg]
  abel

theorem graphCovectorMap_norm_bound (r : Fin d) (b ξ : SpatialCoordinates d) :
    ‖graphCovectorMap r b ξ‖ ≤ (1+‖b‖)*‖ξ‖ := by
  rw [graphCovectorMap_apply]
  calc
    _ ≤ ‖ξ‖+‖ξ r • b‖ := norm_sub_le _ _
    _ ≤ ‖ξ‖+‖ξ‖*‖b‖ := by
      rw [norm_smul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le ξ r) (norm_nonneg _))
    _ = _ := by ring

theorem graphCovectorMap_lower_bound (r : Fin d) (b : SpatialCoordinates d) (hb : b r=0) (ξ : SpatialCoordinates d) :
    ‖ξ‖ ≤ (1+‖b‖)*‖graphCovectorMap r b ξ‖ := by
  have hh := graphCovectorMap_norm_bound r (-b) (graphCovectorMap r b ξ)
  simpa only [graphCovectorMap_inverse r b hb ξ,norm_neg] using hh

def graphMetricEntry (r : Fin d) (b : SpatialCoordinates d) (i j : Fin d) : ℝ :=
  inner ℝ (graphCovectorMap r b (EuclideanSpace.basisFun (Fin d) ℝ i))
    (graphCovectorMap r b (EuclideanSpace.basisFun (Fin d) ℝ j))

theorem graphMetricEntry_energy (r : Fin d) (b ξ : SpatialCoordinates d) :
    (∑ i, ∑ j, graphMetricEntry r b i j*(ξ i)*(ξ j))=‖graphCovectorMap r b ξ‖^2 := by
  have he : ξ=∑ i, (ξ i) • EuclideanSpace.basisFun (Fin d) ℝ i :=
    ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr ξ).symm
  rw [← real_inner_self_eq_norm_sq]
  conv_rhs => rw [he]
  simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold graphMetricEntry
  rw [real_inner_comm (graphCovectorMap r b (EuclideanSpace.basisFun (Fin d) ℝ j))]
  ring


theorem graphMetricEntry_symmetric (r : Fin d) (b : SpatialCoordinates d) (i j : Fin d) :
    graphMetricEntry r b i j=graphMetricEntry r b j i := real_inner_comm _ _

theorem graphMetricEntry_bilinear (r : Fin d) (b ξ η : SpatialCoordinates d) :
    (∑ i, ∑ j, graphMetricEntry r b i j*(ξ i)*(η j))=
      inner ℝ (graphCovectorMap r b ξ) (graphCovectorMap r b η) := by
  have hξ : ξ=∑ i, (ξ i) • EuclideanSpace.basisFun (Fin d) ℝ i :=
    ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr ξ).symm
  have hη : η=∑ i, (η i) • EuclideanSpace.basisFun (Fin d) ℝ i :=
    ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr η).symm
  conv_rhs => rw [hξ,hη]
  simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold graphMetricEntry
  ring

theorem graphMetricEntry_elliptic (r : Fin d) (b : SpatialCoordinates d) (hb : b r=0)
    {D : ℝ} (hD : 0 ≤ D) (hbound : ‖b‖ ≤ D) (ξ : SpatialCoordinates d) :
    ((1+D)^2)⁻¹*(∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, graphMetricEntry r b i j*(ξ i)*(ξ j) := by
  rw [graphMetricEntry_energy,← EuclideanSpace.real_norm_sq_eq]
  have hl := (graphCovectorMap_lower_bound r b hb ξ).trans
    (mul_le_mul_of_nonneg_right (add_le_add_right hbound 1) (norm_nonneg _))
  have hs : ‖ξ‖^2 ≤ (1+D)^2*‖graphCovectorMap r b ξ‖^2 := by nlinarith [norm_nonneg ξ,norm_nonneg (graphCovectorMap r b ξ)]
  have hp : 0 < (1+D)^2 := by positivity
  rw [inv_mul_le_iff₀ hp]
  nlinarith [hs]

def graphSlopeVector (ψ : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : SpatialCoordinates d :=
  ∑ i, (fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ i)) • EuclideanSpace.basisFun (Fin d) ℝ i

theorem graphSlopeVector_apply (ψ : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) (i : Fin d) :
    graphSlopeVector ψ x i=fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  simp [graphSlopeVector,EuclideanSpace.basisFun_apply,Pi.single_apply,mul_ite]

theorem graphSlopeVector_contDiff (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (graphSlopeVector ψ) := by
  apply ContDiff.sum
  intro i _
  exact ((contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const).smul contDiff_const

theorem graphSlopeVector_norm (ψ : SpatialCoordinates d → ℝ) {C : NNReal} (hC : LipschitzWith C ψ)
    (x : SpatialCoordinates d) : ‖graphSlopeVector ψ x‖ ≤ (d : ℝ)*C := by
  calc
    _ ≤ ∑ i, ‖(fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ i)) • EuclideanSpace.basisFun (Fin d) ℝ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (C : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one,mul_one]
      have hh := (fderiv ℝ ψ x).le_opNorm (EuclideanSpace.basisFun (Fin d) ℝ i)
      rw [(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one,mul_one] at hh
      exact hh.trans (norm_fderiv_le_of_lipschitz ℝ hC)
    _ = _ := by simp

theorem graphSlopeVector_lipschitz (ψ : SpatialCoordinates d → ℝ) (B : Fin d → NNReal)
    (hB : ∀ i, LipschitzWith (B i) (fun x => fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ i))) :
    LipschitzWith (∑ i, B i) (graphSlopeVector ψ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  change ‖(∑ i, _) - ∑ i, _‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ i)) • EuclideanSpace.basisFun (Fin d) ℝ i-
        (fderiv ℝ ψ y (EuclideanSpace.basisFun (Fin d) ℝ i)) • EuclideanSpace.basisFun (Fin d) ℝ i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (B i : ℝ)*dist x y := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_smul,norm_smul,(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one,mul_one]
      exact (hB i).dist_le_mul x y
    _ = _ := by simp [Finset.sum_mul]



theorem graphCovectorMap_basis_norm (r : Fin d) (b : SpatialCoordinates d) (i : Fin d) :
    ‖graphCovectorMap r b (EuclideanSpace.basisFun (Fin d) ℝ i)‖ ≤ 1+‖b‖ := by
  simpa only [(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one,mul_one] using
    graphCovectorMap_norm_bound r b (EuclideanSpace.basisFun (Fin d) ℝ i)

theorem graphCovectorMap_basis_sub (r : Fin d) (b c : SpatialCoordinates d) (i : Fin d) :
    ‖graphCovectorMap r b (EuclideanSpace.basisFun (Fin d) ℝ i)-
      graphCovectorMap r c (EuclideanSpace.basisFun (Fin d) ℝ i)‖ ≤ ‖b-c‖ := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ i
  have he : ‖e r‖ ≤ 1 := by simpa only [e,(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one] using PiLp.norm_apply_le e r
  have hh : graphCovectorMap r b e-graphCovectorMap r c e=-(e r • (b-c)) := by
    simp only [graphCovectorMap_apply,smul_sub]
    abel
  rw [hh,norm_neg,norm_smul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg (b-c))

theorem graphMetricEntry_norm (r : Fin d) (b : SpatialCoordinates d) (i j : Fin d) :
    |graphMetricEntry r b i j| ≤ (1+‖b‖)^2 := by
  apply (abs_real_inner_le_norm _ _).trans
  calc
    _ ≤ (1+‖b‖)*(1+‖b‖) := mul_le_mul (graphCovectorMap_basis_norm r b i)
      (graphCovectorMap_basis_norm r b j) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem graphMetricEntry_sub_bound (r : Fin d) (b c : SpatialCoordinates d) {D : ℝ}
    (hb : ‖b‖ ≤ D) (hc : ‖c‖ ≤ D) (i j : Fin d) :
    |graphMetricEntry r b i j-graphMetricEntry r c i j| ≤ 2*(1+D)*‖b-c‖ := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  let X := graphCovectorMap r b (e i)
  let Y := graphCovectorMap r b (e j)
  let V := graphCovectorMap r c (e i)
  let W := graphCovectorMap r c (e j)
  have hn : 0 ≤ 1+D := by linarith [norm_nonneg b]
  have hY : ‖Y‖ ≤ 1+D := (graphCovectorMap_basis_norm r b j).trans (by linarith)
  have hV : ‖V‖ ≤ 1+D := (graphCovectorMap_basis_norm r c i).trans (by linarith)
  have hx : ‖X-V‖ ≤ ‖b-c‖ := graphCovectorMap_basis_sub r b c i
  have hy : ‖Y-W‖ ≤ ‖b-c‖ := graphCovectorMap_basis_sub r b c j
  have hid : graphMetricEntry r b i j-graphMetricEntry r c i j=
      inner ℝ (X-V) Y+inner ℝ V (Y-W) := by
    simp only [inner_sub_left,inner_sub_right]
    change inner ℝ X Y-inner ℝ V W= _
    ring
  rw [hid]
  calc
    _ ≤ |inner ℝ (X-V) Y|+|inner ℝ V (Y-W)| := abs_add_le _ _
    _ ≤ ‖X-V‖*‖Y‖+‖V‖*‖Y-W‖ := add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖b-c‖*(1+D)+(1+D)*‖b-c‖ := add_le_add
      (mul_le_mul hx hY (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul hV hy (norm_nonneg _) hn)
    _ = _ := by ring

theorem graphMetricEntry_contDiff (r : Fin d) (b : SpatialCoordinates d → SpatialCoordinates d)
    (hb : ContDiff ℝ ∞ b) (i j : Fin d) : ContDiff ℝ ∞ (fun x => graphMetricEntry r (b x) i j) := by
  have hh (k : Fin d) : ContDiff ℝ ∞ (fun x => EuclideanSpace.basisFun (Fin d) ℝ k-
      (EuclideanSpace.basisFun (Fin d) ℝ k r) • b x) :=
    contDiff_const.sub (ContDiff.const_smul (EuclideanSpace.basisFun (Fin d) ℝ k r) hb)
  exact (hh i).inner ℝ (hh j)

theorem graphMetricEntry_lipschitz (r : Fin d) (b : SpatialCoordinates d → SpatialCoordinates d)
    {D L : NNReal} (hb : ∀ x, ‖b x‖ ≤ D) (hL : LipschitzWith L b) (i j : Fin d) :
    LipschitzWith (2*(1+D)*L) (fun x => graphMetricEntry r (b x) i j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  calc
    _ ≤ 2*(1+(D : ℝ))*‖b x-b y‖ := graphMetricEntry_sub_bound r (b x) (b y) (hb x) (hb y) i j
    _ ≤ 2*(1+(D : ℝ))*((L : ℝ)*dist x y) := mul_le_mul_of_nonneg_left (hL.dist_le_mul x y) (by positivity)
    _ = _ := by simp [mul_assoc]

def graphEllipticCoefficient (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ) (i j : Fin d) :
    BoundedMultiplier (volume : Measure (SpatialCoordinates d)) where
  value x := graphMetricEntry r (graphSlopeVector ψ x) i j
  measurable := (graphMetricEntry_contDiff r _ (graphSlopeVector_contDiff ψ hψ) i j).continuous.aestronglyMeasurable
  bound := (1+(d : ℝ)*C)^2
  bound_nonneg := sq_nonneg _
  bounded := Eventually.of_forall fun x => (graphMetricEntry_norm r _ i j).trans
    (by have hh := graphSlopeVector_norm ψ hC x; nlinarith [norm_nonneg (graphSlopeVector ψ x)])

theorem graphEllipticCoefficient_contDiff (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ) (i j : Fin d) :
    ContDiff ℝ ∞ (graphEllipticCoefficient r ψ hψ hC i j).value :=
  graphMetricEntry_contDiff r _ (graphSlopeVector_contDiff ψ hψ) i j

theorem graphEllipticCoefficient_lipschitz (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ) (B : Fin d → NNReal)
    (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value) (i j : Fin d) :
    LipschitzWith (2*(1+(d : NNReal)*C)*(∑ k, B k)) (graphEllipticCoefficient r ψ hψ hC i j).value := by
  apply graphMetricEntry_lipschitz
  · intro x
    exact_mod_cast graphSlopeVector_norm ψ hC x
  · exact graphSlopeVector_lipschitz ψ B hB

theorem graphEllipticCoefficient_elliptic (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    ∀ x, ∀ ξ : Fin d → ℝ,
      ((1+(d : ℝ)*C)^2)⁻¹*(∑ i, (ξ i)^2) ≤
        ∑ i, ∑ j, (graphEllipticCoefficient r ψ hψ hC i j).value x*(ξ i)*(ξ j) := by
  intro x ξ
  apply graphMetricEntry_elliptic r _ _ (by positivity) (graphSlopeVector_norm ψ hC x) (WithLp.toLp 2 ξ)
  rw [graphSlopeVector_apply]
  exact spatialGraphShear_normal_derivative r ψ hψ htrans x


theorem graphMetricEntry_bilinear_coordinates (r : Fin d) (b : SpatialCoordinates d) (ξ η : Fin d → ℝ) :
    (∑ i, ∑ j, graphMetricEntry r b i j*(ξ i)*(η j))=
      ∑ k, (ξ k-ξ r*b k)*(η k-η r*b k) := by
  have he := graphMetricEntry_bilinear r b (WithLp.toLp 2 ξ) (WithLp.toLp 2 η)
  rw [PiLp.inner_apply] at he
  simp only [graphCovectorMap_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    RCLike.inner_apply,conj_trivial] at he
  simpa only [mul_comm] using he

theorem graphEllipticCoefficient_pairing {S : Set (SpatialCoordinates d)}
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (G H : Fin d → Lp ℝ 2 (volume.restrict S)) :
    let a i j := (graphEllipticCoefficient r ψ hψ hC i j).restrictMeasure (ν := volume.restrict S) Measure.restrict_le_self
    let w i := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure (ν := volume.restrict S) Measure.restrict_le_self
    matrixL2Pairing a G H=∑ i, inner ℝ (G i-(w i).map (G r)) (H i-(w i).map (H r)) := by
  let a i j := (graphEllipticCoefficient r ψ hψ hC i j).restrictMeasure (ν := volume.restrict S) Measure.restrict_le_self
  let w i := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure (ν := volume.restrict S) Measure.restrict_le_self
  let V i := G i-(w i).map (G r)
  let W i := H i-(w i).map (H r)
  change matrixL2Pairing a G H=∑ i, inner ℝ (V i) (W i)
  have hl : matrixL2Pairing a G H=
      ∫ x, ∑ i, ∑ j, inner ℝ ((a i j).map (G i) x) (H j x) ∂volume.restrict S := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => L2.integrable_inner _ _)]
    unfold matrixL2Pairing
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => L2.integrable_inner _ _)]
    simp only [L2.inner_def]
  have hr : (∑ i, inner ℝ (V i) (W i))=
      ∫ x, ∑ i, inner ℝ (V i x) (W i x) ∂volume.restrict S := by
    rw [integral_finsetSum _ (fun i _ => L2.integrable_inner _ _)]
    simp only [L2.inner_def]
  rw [hl,hr]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => (a i j).map_ae (G i))),
    ae_all_iff.mpr (fun i => (w i).map_ae (G r)),ae_all_iff.mpr (fun i => (w i).map_ae (H r)),
    ae_all_iff.mpr (fun i => Lp.coeFn_sub (G i) ((w i).map (G r))),
    ae_all_iff.mpr (fun i => Lp.coeFn_sub (H i) ((w i).map (H r)))] with x ha hwg hwh hvg hvh
  calc
    _ = ∑ i, ∑ j, graphMetricEntry r (graphSlopeVector ψ x) i j*(G i x)*(H j x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [ha i j]
      simp only [RCLike.inner_apply,conj_trivial,smul_eq_mul]
      change H j x*((graphMetricEntry r (graphSlopeVector ψ x) i j)*G i x)=_
      ring
    _ = ∑ i, (G i x-G r x*(graphSlopeVector ψ x i))*(H i x-H r x*(graphSlopeVector ψ x i)) :=
      graphMetricEntry_bilinear_coordinates r _ (fun i => G i x) (fun i => H i x)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show V i x=(G i-(w i).map (G r)) x from rfl,hvg i,
        show W i x=(H i-(w i).map (H r)) x from rfl,hvh i]
      simp only [Pi.sub_apply,hwg i,hwh i,RCLike.inner_apply,conj_trivial,smul_eq_mul,graphSlopeVector_apply]
      change (_-_*_)*(_-_*_)=(_-(fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ i))*_)*
        (_-(fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ i))*_)
      ring

namespace WeakSobolevJet
variable {T : Set (SpatialCoordinates d)}

theorem graphShearPullback_inverse_gradient (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (i : Fin d) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
    let w := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self
    let U := graphShearPullback hT r ψ hψ hC htrans u
    derivativeComponent (Sym.cons i Sym.nil) (field 1 U)-
      w.map (derivativeComponent (Sym.cons r Sym.nil) (field 1 U))=
      P (derivativeComponent (Sym.cons i Sym.nil) (field 1 u)) := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
  let w j := (graphSlopeMultiplier ψ hψ hC j).restrictMeasure (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self
  let g j := P (derivativeComponent (Sym.cons j Sym.nil) (field 1 u))
  have hz : (w r).map (g r)=0 := by
    apply Lp.ext
    filter_upwards [(w r).map_ae (g r),Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict (F ⁻¹' T))] with x hx h0
    rw [hx,h0]
    change (fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin d) ℝ r)) • g r x=0
    rw [spatialGraphShear_normal_derivative r ψ hψ htrans,zero_smul]
  change _-(w i).map _=g i
  rw [graphShearPullback_gradient,graphShearPullback_gradient]
  change g i+(w i).map (g r)-(w i).map (g r+(w r).map (g r))=g i
  rw [hz,add_zero,add_sub_cancel_right]

end WeakSobolevJet



theorem graphShearPullback_energy {T : Set (SpatialCoordinates d)} (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (u v : WeakSobolevJet d 1 (volume.restrict T) T) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    let a i j := (graphEllipticCoefficient r ψ hψ hC i j).restrictMeasure (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self
    matrixGradientPairing a (WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u)
      (WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans v)=weakGradientPairing u v := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
  dsimp only
  unfold matrixGradientPairing
  rw [graphEllipticCoefficient_pairing,weakGradientPairing_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [WeakSobolevJet.graphShearPullback_inverse_gradient,WeakSobolevJet.graphShearPullback_inverse_gradient]
  exact P.inner_map_map _ _

theorem graphShearPullback_equation {T : Set (SpatialCoordinates d)} (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (f : Lp ℝ 2 (volume.restrict T))
    (hf : IsWeakNegativeLaplacian u f) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
    let a i j := (graphEllipticCoefficient r ψ hψ hC i j).restrictMeasure (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self
    ∀ φ : SpatialTest (F ⁻¹' T),
      matrixGradientPairing a (WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u) φ.sobolevJet=
        inner ℝ (P f) (φ.toLp (volume.restrict (F ⁻¹' T))) := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let hm := spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T
  let P := homeomorphPullbackLp F hm
  let S := F ⁻¹' T
  let a i j := (graphEllipticCoefficient r ψ hψ hC i j).restrictMeasure (ν := volume.restrict S) Measure.restrict_le_self
  change ∀ φ : SpatialTest S, matrixGradientPairing a (WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u) φ.sobolevJet=
    inner ℝ (P f) (φ.toLp (volume.restrict S))
  intro φ
  have hS : IsOpen S := hT.preimage F.continuous
  have hST : F.symm ⁻¹' S ⊆ T := by
    intro x hx
    change F (F.symm x) ∈ T at hx
    simpa only [F.apply_symm_apply] using hx
  let χ := φ.pullbackSmoothHomeomorph F.symm (spatialGraphShear_symm_contDiff r ψ hψ htrans) hST
  have hv : P (χ.toLp (volume.restrict T))=φ.toLp (volume.restrict S) := by
    apply Lp.ext
    filter_upwards [homeomorphPullbackLp_ae F hm (χ.toLp (volume.restrict T)),
      hm.quasiMeasurePreserving.ae (χ.toLp_ae (volume.restrict T)),φ.toLp_ae (volume.restrict S)] with x hx hy hz
    rw [hx]
    change χ.toLp (volume.restrict T) (F x)=_
    rw [hy,hz]
    exact congrArg φ.value (F.symm_apply_apply x)
  have hχ : WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans χ.sobolevJet=φ.sobolevJet := by
    apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
    rw [WeakSobolevJet.graphShearPullback_value,χ.sobolevJet_value,φ.sobolevJet_value]
    exact hv
  have he := graphShearPullback_energy hT r ψ hψ hC htrans u χ.sobolevJet
  rw [hχ] at he
  change matrixGradientPairing a _ _=_ at he
  rw [he,hf χ,← P.inner_map_map f (χ.toLp (volume.restrict T)),hv]

theorem graphShearPullback_equation_integral {T : Set (SpatialCoordinates d)} (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (f : Lp ℝ 2 (volume.restrict T))
    (hf : IsWeakNegativeLaplacian u f) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
    let U := WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u
    ∀ φ : SpatialTest (F ⁻¹' T),
      (∑ i, ∑ j, ∫ x in F ⁻¹' T, (graphEllipticCoefficient r ψ hψ hC i j).value x*
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 U) x)*
        (fderiv ℝ φ.value x (EuclideanSpace.basisFun (Fin d) ℝ j)))=
        inner ℝ (P f) (φ.toLp (volume.restrict (F ⁻¹' T))) := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let U := WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u
  change ∀ φ : SpatialTest (F ⁻¹' T), _
  intro φ
  rw [← graphShearPullback_equation hT r ψ hψ hC htrans u f hf φ]
  unfold matrixGradientPairing matrixL2Pairing
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [SpatialTest.sobolevJet_derivative φ j]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((graphEllipticCoefficient r ψ hψ hC i j).restrictMeasure (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self).map_ae
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 U)),
    φ.derivativeLp_ae (volume.restrict (F ⁻¹' T)) (EuclideanSpace.basisFun (Fin d) ℝ j)] with x hx hd
  rw [hx,hd]
  simp only [RCLike.inner_apply,conj_trivial,smul_eq_mul,BoundedMultiplier.restrictMeasure]
  ring


end Carleman
