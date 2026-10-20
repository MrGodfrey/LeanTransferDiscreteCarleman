module
public import Carleman.Geometry.LevelBoundaryHessian
public import Carleman.Spatial.GraphEllipticForm
/-! The actual Miranda–Talenti flux on a convex level boundary. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem euclidean_coordinate_expansion (v : SpatialCoordinates d) :
    ∑ i, v i • EuclideanSpace.basisFun (Fin d) ℝ i=v := by
  simpa only [EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v

theorem graphSlopeVector_inner (f : SpatialCoordinates d → ℝ) (c v : SpatialCoordinates d) :
    inner ℝ (graphSlopeVector f c) v=fderiv ℝ f c v := by
  rw [graphSlopeVector,sum_inner]
  simp only [real_inner_smul_left,EuclideanSpace.basisFun_inner]
  nth_rw 2 [← euclidean_coordinate_expansion v]
  simp only [map_sum,map_smul,smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem graphSlopeVector_ne_zero {g : SpatialCoordinates d → ℝ} {c : SpatialCoordinates d}
    (hreg : fderiv ℝ g c ≠ 0) : graphSlopeVector g c ≠ 0 := by
  intro h
  apply hreg
  ext v
  rw [← graphSlopeVector_inner,h]
  simp

theorem graphSlopeVector_multiple (u g : SpatialCoordinates d → ℝ) (c : SpatialCoordinates d)
    (q : ℝ) (h : fderiv ℝ u c=q • fderiv ℝ g c) :
    graphSlopeVector u c=q • graphSlopeVector g c := by
  ext i
  simp only [graphSlopeVector_apply,PiLp.smul_apply,smul_eq_mul]
  rw [h]
  rfl

def scaledLevelTangent (N : SpatialCoordinates d) (i : Fin d) : SpatialCoordinates d :=
  ‖N‖^2 • EuclideanSpace.basisFun (Fin d) ℝ i-N i • N

theorem scaledLevelTangent_inner (N : SpatialCoordinates d) (i : Fin d) :
    inner ℝ N (scaledLevelTangent N i)=0 := by
  simp only [scaledLevelTangent,inner_sub_right,real_inner_smul_right,
    EuclideanSpace.inner_basisFun_real,real_inner_self_eq_norm_sq]
  ring

theorem bilinear_scaled_tangent_sum
    (H : SpatialCoordinates d →L[ℝ] SpatialCoordinates d →L[ℝ] ℝ)
    (N : SpatialCoordinates d) :
    ∑ i, H (scaledLevelTangent N i) (scaledLevelTangent N i)=
      ‖N‖^2*(‖N‖^2*(∑ i, H (EuclideanSpace.basisFun (Fin d) ℝ i)
        (EuclideanSpace.basisFun (Fin d) ℝ i))-H N N) := by
  have h1 : ∑ i, N i*H (EuclideanSpace.basisFun (Fin d) ℝ i) N=H N N := by
    have he := congrArg (fun v => H v N) (euclidean_coordinate_expansion N)
    simpa only [map_sum,sum_apply,map_smul,smul_apply,smul_eq_mul] using he
  have h2 : ∑ i, N i*H N (EuclideanSpace.basisFun (Fin d) ℝ i)=H N N := by
    have he := congrArg (fun v => H N v) (euclidean_coordinate_expansion N)
    simpa only [map_sum,map_smul,smul_eq_mul] using he
  have h3 : ∑ i, (N i)^2=‖N‖^2 := (EuclideanSpace.real_norm_sq_eq N).symm
  calc
    _ = ∑ i, (‖N‖^4*H (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i)-
        ‖N‖^2*(N i*H (EuclideanSpace.basisFun (Fin d) ℝ i) N)-
        ‖N‖^2*(N i*H N (EuclideanSpace.basisFun (Fin d) ℝ i))+(N i)^2*H N N) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [scaledLevelTangent,map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
        ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,← Finset.sum_mul,h1,h2,h3]
      ring

theorem spatialLaplacian_eq_hessian_trace (u : SpatialCoordinates d → ℝ)
    (hu : ContDiff ℝ ∞ u) (c : SpatialCoordinates d) :
    spatialLaplacian u c=∑ i, fderiv ℝ (fderiv ℝ u) c
      (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  exact Finset.sum_congr rfl fun i _ => smooth_directional_fderiv_eq u hu c _ _

def levelBoundaryFlux (u g : SpatialCoordinates d → ℝ) (c : SpatialCoordinates d) : ℝ :=
  spatialLaplacian u c*inner ℝ (graphSlopeVector u c) (graphSlopeVector g c)-
    fderiv ℝ (fderiv ℝ u) c (graphSlopeVector u c) (graphSlopeVector g c)

theorem spatialLaplacian_contDiff (u : SpatialCoordinates d → ℝ)
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (spatialLaplacian u) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) := hD.fderiv_right (by simp)
  have he : spatialLaplacian u=fun c => ∑ i, fderiv ℝ (fderiv ℝ u) c
      (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i) :=
    funext (spatialLaplacian_eq_hessian_trace u hu)
  rw [he]
  exact ContDiff.sum fun i _ => (hDD.clm_apply contDiff_const).clm_apply contDiff_const

theorem levelBoundaryFlux_contDiff (u g : SpatialCoordinates d → ℝ)
    (hu : ContDiff ℝ ∞ u) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (levelBoundaryFlux u g) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) := hD.fderiv_right (by simp)
  exact ((spatialLaplacian_contDiff u hu).mul
    ((graphSlopeVector_contDiff u hu).inner ℝ (graphSlopeVector_contDiff g hg))).sub
    ((hDD.clm_apply (graphSlopeVector_contDiff u hu)).clm_apply (graphSlopeVector_contDiff g hg))

theorem levelBoundaryFlux_scaled_identity (u g : SpatialCoordinates d → ℝ)
    (hu : ContDiff ℝ ∞ u) (c : SpatialCoordinates d) (q : ℝ)
    (hgrad : fderiv ℝ u c=q • fderiv ℝ g c)
    (hH : ∀ v : SpatialCoordinates d, fderiv ℝ g c v=0 →
      fderiv ℝ (fderiv ℝ u) c v v=q*fderiv ℝ (fderiv ℝ g) c v v) :
    ‖graphSlopeVector g c‖^2*levelBoundaryFlux u g c=
      q^2*∑ i, fderiv ℝ (fderiv ℝ g) c
        (scaledLevelTangent (graphSlopeVector g c) i) (scaledLevelTangent (graphSlopeVector g c) i) := by
  let N := graphSlopeVector g c
  have ht (i : Fin d) : fderiv ℝ g c (scaledLevelTangent N i)=0 := by
    rw [← graphSlopeVector_inner]
    exact scaledLevelTangent_inner N i
  have hs : ∑ i, fderiv ℝ (fderiv ℝ u) c (scaledLevelTangent N i) (scaledLevelTangent N i)=
      q*∑ i, fderiv ℝ (fderiv ℝ g) c (scaledLevelTangent N i) (scaledLevelTangent N i) := by
    simp only [hH _ (ht _),Finset.mul_sum]
  rw [bilinear_scaled_tangent_sum,← spatialLaplacian_eq_hessian_trace u hu] at hs
  unfold levelBoundaryFlux
  rw [graphSlopeVector_multiple u g c q hgrad]
  simp only [real_inner_smul_left,real_inner_self_eq_norm_sq,map_smul,smul_apply,smul_eq_mul]
  change ‖N‖^2*(spatialLaplacian u c*(q*‖N‖^2)-q*fderiv ℝ (fderiv ℝ u) c N N)=_
  linear_combination q*hs

theorem levelBoundaryFlux_nonneg (u g : SpatialCoordinates d → ℝ)
    (hu : ContDiff ℝ ∞ u) (c : SpatialCoordinates d)
    (hreg : fderiv ℝ g c ≠ 0)
    (hdata : ∃ q : ℝ, fderiv ℝ u c=q • fderiv ℝ g c ∧
      ∀ v : SpatialCoordinates d, fderiv ℝ g c v=0 →
        fderiv ℝ (fderiv ℝ u) c v v=q*fderiv ℝ (fderiv ℝ g) c v v)
    (hconv : ∀ v : SpatialCoordinates d, 0≤fderiv ℝ (fderiv ℝ g) c v v) :
    0≤levelBoundaryFlux u g c := by
  obtain ⟨q,hgrad,hH⟩ := hdata
  have hp : 0<‖graphSlopeVector g c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (graphSlopeVector_ne_zero hreg))
  have hh : 0≤‖graphSlopeVector g c‖^2*levelBoundaryFlux u g c := by
    rw [levelBoundaryFlux_scaled_identity u g hu c q hgrad hH]
    exact mul_nonneg (sq_nonneg q) (Finset.sum_nonneg fun i _ => hconv _)
  exact nonneg_of_mul_nonneg_right hh hp

theorem halfspaceSmoothInner_boundaryFlux_nonneg {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    {z : SpatialCoordinates d} (hz : z ∈ halfspaceSmoothInner ℓ b n)
    (u : SpatialCoordinates d → ℝ) (hu : ContDiff ℝ ∞ u)
    (hzero : ∀ x ∈ frontier (halfspaceSmoothInner ℓ b n), u x=0)
    {c : SpatialCoordinates d} (hc : c ∈ frontier (halfspaceSmoothInner ℓ b n)) :
    0≤levelBoundaryFlux u (halfspaceExpSum ℓ b n) c := by
  exact levelBoundaryFlux_nonneg u (halfspaceExpSum ℓ b n) hu c
    (halfspaceSmoothInner_boundary_regular ℓ b n hz hc).2
    (halfspaceSmoothInner_zero_gradient_hessian ℓ b n hz u hu hzero hc)
    (halfspaceExpSum_hessian_nonneg ℓ b n c)
end Carleman
