module

public import Carleman.Spatial.ConvexSegmentIntegral
public import Carleman.Spatial.StrongMollifierLimit
public import Carleman.Spatial.ContractionSequence

/-! Actual scalar affine pullbacks preserve L², with the genuine volume
Jacobian. The inward sequence has a dimension-only operator bound. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem scalarAffine_memLp {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 volume)
    {r : ℝ} (hr : 0 < r) (b : SpatialCoordinates d) :
    MemLp (fun x => f (r • x+b)) 2 volume := by
  let A := (LinearEquiv.smulOfNeZero ℝ (SpatialCoordinates d) r hr.ne').toContinuousLinearEquiv
  have hm : MemLp f 2 (Measure.map (affineChange A b) volume) := by
    rw [affineChange_map_volume]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map (affineChange A b).continuous.measurable.aemeasurable

theorem integral_scalarAffine_univ (f : SpatialCoordinates d → ℝ)
    {r : ℝ} (hr : 0 < r) (b : SpatialCoordinates d) :
    (∫ x, f (r • x+b)) = (r^d)⁻¹*(∫ x, f x) := by
  have hsurj : Function.Surjective (fun x : SpatialCoordinates d => r • x+b) := by
    intro y
    refine ⟨r⁻¹ • (y-b),?_⟩
    simp [smul_smul,hr.ne']
  simpa only [Set.image_univ_of_surjective hsurj,Measure.restrict_univ] using
    integral_comp_scalar_affine Set.univ f hr b

theorem scalarAffine_L2_sq {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 volume)
    {r : ℝ} (hr : 0 < r) (b : SpatialCoordinates d) :
    (bochnerL2Norm volume (fun x => f (r • x+b)))^2 = (r^d)⁻¹*(bochnerL2Norm volume f)^2 := by
  rw [← integral_sq_eq_bochnerL2Norm_sq (scalarAffine_memLp hf hr b),
    ← integral_sq_eq_bochnerL2Norm_sq hf]
  exact integral_scalarAffine_univ (fun x => (f x)^2) hr b

def inwardPullback (a : SpatialCoordinates d) (n : ℕ) (f : SpatialCoordinates d → ℝ) :
    SpatialCoordinates d → ℝ := fun x => f (inwardRatio n • x+(1-inwardRatio n) • a)

theorem inwardPullback_memLp (a : SpatialCoordinates d) (n : ℕ)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 volume) :
    MemLp (inwardPullback a n f) 2 volume :=
  scalarAffine_memLp hf (inwardRatio_pos n) _

theorem inwardPullback_L2_le (a : SpatialCoordinates d) (n : ℕ)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 volume) :
    bochnerL2Norm volume (inwardPullback a n f) ≤ (2:ℝ)^d*bochnerL2Norm volume f := by
  have hp : ((inwardRatio n)^d)⁻¹ ≤ (2:ℝ)^d := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (inwardRatio_pos n).le) (inwardRatio_inv_le_two n) d
  have hC : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
  apply (sq_le_sq₀ (bochnerL2Norm_nonneg _) (mul_nonneg (by positivity) (bochnerL2Norm_nonneg _))).mp
  change (bochnerL2Norm volume (fun x => f (inwardRatio n • x+(1-inwardRatio n) • a)))^2 ≤ _
  rw [scalarAffine_L2_sq hf (inwardRatio_pos n),mul_pow]
  have ht : ((inwardRatio n)^d)⁻¹ ≤ ((2:ℝ)^d)^2 := by nlinarith
  exact mul_le_mul_of_nonneg_right ht (sq_nonneg _)

theorem inwardPoint_tendsto (a x : SpatialCoordinates d) :
    Tendsto (fun n => inwardRatio n • x+(1-inwardRatio n) • a) atTop (𝓝 x) := by
  simpa using (inwardRatio_tendsto.smul_const x).add
    (((tendsto_const_nhds (x := (1:ℝ))).sub inwardRatio_tendsto).smul_const a)

end Carleman
