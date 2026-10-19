module

public import Carleman.Spatial.SpatialTestLpDensity
public import Carleman.Spatial.DenseReconstructionConvergence
public import Carleman.Spatial.SimplexNodalRemainder
public import Carleman.Spatial.SimplicialDiameter
public import Carleman.Spatial.NodalDirichletMembership

/-! Strong consistency of the original full conforming P1 L² projection for every L² initial datum. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} [IsFiniteMeasure (volume.restrict S)]
namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] (M : Carleman.SimplicialPartition S ι)

omit [IsFiniteMeasure (volume.restrict S)] in
theorem nodal_lipschitz_value_error (hM : M.FaceMatching) (f : SpatialCoordinates d → ℝ)
    {C : ℝ≥0} (hf : LipschitzWith C f) (i : ι) {x : SpatialCoordinates d} (hx : x ∈ M.cell i) :
    |f x-M.nodalFunction f x| ≤ 2*C*M.maxDiameter := by
  rw [M.nodalFunction_on_cell hM f i hx]
  let a := (M.simplex i).points 0
  have ha : a ∈ M.cell i := subset_convexHull ℝ _ (Set.mem_range_self 0)
  have hb : ∀ y ∈ M.cell i, |f y-(AffineMap.const ℝ (SpatialCoordinates d) (f a)) y| ≤ C*M.maxDiameter := by
    intro y hy
    change |f y-f a| ≤ C*M.maxDiameter
    have hdist := (M.dist_le_cellDiameter i hy ha).trans (M.cellDiameter_le_max i)
    exact (hf.dist_le_mul y a).trans (mul_le_mul_of_nonneg_left hdist C.coe_nonneg)
  simpa only [localNodal,mul_assoc] using simplexNodal_error_of_affine_approximation (M.simplex i) f
    (AffineMap.const ℝ (SpatialCoordinates d) (f a)) hb hx

theorem test_nodal_L2_error (hS : IsOpen S) (hM : M.FaceMatching)
    (φ : SpatialTest S) {C : ℝ≥0} (hφ : LipschitzWith C φ.value) :
    ‖φ.toLp (volume.restrict S)-M.nodalLp hS.measurableSet hM φ.value‖ ≤
      (measureUnivNNReal (volume.restrict S) : ℝ)^((2:ENNReal).toReal⁻¹)*(2*C*M.maxDiameter) := by
  apply Lp.norm_le_of_ae_bound (by positivity [M.maxDiameter_nonneg])
  filter_upwards [φ.toLp_ae (volume.restrict S),M.nodalLp_ae hS.measurableSet hM φ.value,
    Lp.coeFn_sub (φ.toLp (volume.restrict S)) (M.nodalLp hS.measurableSet hM φ.value),
    M.ae_partition hS.measurableSet] with x hφx hIx hsub hx
  rw [hsub,Pi.sub_apply,hφx,hIx,Real.norm_eq_abs]
  obtain ⟨i,hi,_⟩ := hx
  exact M.nodal_lipschitz_value_error hM φ.value hφ i hi

theorem test_projection_L2_error (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (φ : SpatialTest S) {C : ℝ≥0} (hφ : LipschitzWith C φ.value) :
    ‖φ.toLp (volume.restrict S)-
      ((M.conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto (φ.toLp (volume.restrict S)) :
        Lp ℝ 2 (volume.restrict S))‖ ≤
      (measureUnivNNReal (volume.restrict S) : ℝ)^((2:ENNReal).toReal⁻¹)*(2*C*M.maxDiameter) := by
  let X := M.conformingSpace (dirichletSubspace S)
  have hI : M.nodalLp hS.measurableSet hM φ.value ∈ X := by
    apply M.nodalLp_mem_dirichletConformingSpace hS hc hM hB
    intro i k hk
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    exact hk.2 (hS.interior_eq.symm ▸ φ.support hx)
  have hb := reconstruction_best_approximation X.subtypeₗᵢ (φ.toLp (volume.restrict S))
    ⟨M.nodalLp hS.measurableSet hM φ.value,hI⟩
  change ‖φ.toLp (volume.restrict S)-X.subtypeL (X.subtypeL.adjoint (φ.toLp (volume.restrict S)))‖ ≤ _ at hb
  rw [Submodule.adjoint_subtypeL] at hb
  exact hb.trans (M.test_nodal_L2_error hS hM φ hφ)

end SimplicialPartition

set_option maxHeartbeats 1200000 in
theorem full_p1_initial_projection_strong_convergence (hS : IsOpen S) (hc : Convex ℝ S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    (hM : ∀ n, (M n).FaceMatching) (hB : ∀ n, (M n).BoundaryFitted)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0))
    (u : Lp ℝ 2 (volume.restrict S)) :
    Tendsto (fun n => (((M n).conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto u :
      Lp ℝ 2 (volume.restrict S))) atTop (𝓝 u) := by
  let X n := (M n).conformingSpace (dirichletSubspace S)
  have hh := isometric_reconstruction_tendsto_of_denseRange (fun n => (X n).subtypeₗᵢ)
    (fun φ : SpatialTest S => φ.toLp (volume.restrict S)) (spatialTest_toLp_denseRange hS)
  have htest : ∀ φ : SpatialTest S, Tendsto (fun n =>
      ‖φ.toLp (volume.restrict S)-(X n).subtypeL ((X n).subtypeL.adjoint (φ.toLp (volume.restrict S)))‖)
      atTop (𝓝 0) := by
    intro φ
    obtain ⟨C,hφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.compact φ.smooth (by simp)
    simp_rw [Submodule.adjoint_subtypeL]
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => (M n).test_projection_L2_error hS hc (hM n) (hB n) φ hφ)
    simpa using (tendsto_const_nhds (x := (measureUnivNNReal (volume.restrict S):ℝ)^((2:ENNReal).toReal⁻¹))).mul
      ((tendsto_const_nhds (x := 2*(C:ℝ))).mul hlim)
  have hh' := hh htest u
  change Tendsto (fun n => (X n).subtypeL ((X n).subtypeL.adjoint u)) atTop (𝓝 u) at hh'
  simpa only [Submodule.adjoint_subtypeL,Submodule.subtypeL_apply,X] using hh'

end Carleman
