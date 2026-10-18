module

public import Carleman.Spatial.SimplicialNodalLp

/-! Exact global nodal interpolation as a linear map on pointwise functions.
There is no evaluation map on L² classes and no Sobolev claim. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

theorem nodalFunction_congr {f g : SpatialCoordinates d → ℝ}
    (h : ∀ i k, f ((M.simplex i).points k) = g ((M.simplex i).points k)) :
    M.nodalFunction f = M.nodalFunction g := by
  funext x
  unfold nodalFunction
  split
  · simp only [localNodal,simplexNodalInterpolant_apply,h]
  · rfl

theorem nodalFunction_add (f g : SpatialCoordinates d → ℝ) :
    M.nodalFunction (f+g) = M.nodalFunction f + M.nodalFunction g := by
  funext x
  classical
  by_cases hx : ∃ i, x ∈ M.cell i
  · simp only [nodalFunction,dite_eq_left hx,localNodal,simplexNodalInterpolant_apply,
      Pi.add_apply,add_mul,Finset.sum_add_distrib]
  · simp only [nodalFunction,dite_eq_right hx,Pi.add_apply,add_zero]

theorem nodalFunction_smul (c : ℝ) (f : SpatialCoordinates d → ℝ) :
    M.nodalFunction (c • f) = c • M.nodalFunction f := by
  funext x
  classical
  by_cases hx : ∃ i, x ∈ M.cell i
  · simp only [nodalFunction,dite_eq_left hx,localNodal,simplexNodalInterpolant_apply,
      Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]
  · simp only [nodalFunction,dite_eq_right hx,Pi.smul_apply,smul_eq_mul,mul_zero]

def nodalFunctionLinearMap : (SpatialCoordinates d → ℝ) →ₗ[ℝ] (SpatialCoordinates d → ℝ) where
  toFun := M.nodalFunction
  map_add' := M.nodalFunction_add
  map_smul' := M.nodalFunction_smul

/-- Uniqueness holds for actual pointwise piecewise affine functions. -/
theorem nodalFunction_unique (hM : M.FaceMatching) (f g : SpatialCoordinates d → ℝ)
    (hg : ∀ i, ∃ p : SpatialCoordinates d →ᵃ[ℝ] ℝ, (M.cell i).EqOn g p)
    (hnode : ∀ i k, g ((M.simplex i).points k) = f ((M.simplex i).points k))
    (i : ι) {x : SpatialCoordinates d} (hx : x ∈ M.cell i) :
    M.nodalFunction f x = g x := by
  obtain ⟨p,hp⟩ := hg i
  rw [M.nodalFunction_on_cell hM f i hx]
  have hv : (fun k => f ((M.simplex i).points k)) = (fun k => p ((M.simplex i).points k)) := by
    funext k
    exact (hnode i k).symm.trans (hp (subset_convexHull ℝ _ (Set.mem_range_self k)))
  change simplexNodalInterpolant (M.simplex i) _ x = _
  rw [hv,simplexNodalInterpolant_reproduces]
  exact (hp hx).symm

theorem nodalFunction_idempotent (hM : M.FaceMatching) (f : SpatialCoordinates d → ℝ) :
    M.nodalFunction (M.nodalFunction f) = M.nodalFunction f :=
  M.nodalFunction_congr (fun i k => M.nodalFunction_vertex hM f i k)

variable [Fintype ι]

/-- The stability constant is exactly one on the closed domain. -/
theorem nodalFunction_abs_le (hM : M.FaceMatching) (f : SpatialCoordinates d → ℝ) (C : ℝ)
    (hc : ∀ i k, |f ((M.simplex i).points k)| ≤ C)
    {x : SpatialCoordinates d} (hx : x ∈ closure S) : |M.nodalFunction f x| ≤ C := by
  rw [← M.cells_union] at hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  rw [M.nodalFunction_on_cell hM f i hi]
  exact simplexNodalInterpolant_abs_le _ _ C (hc i) hi

variable [IsFiniteMeasure (volume.restrict S)]

theorem nodalLp_congr (hS : MeasurableSet S) (hM : M.FaceMatching)
    {f g : SpatialCoordinates d → ℝ}
    (h : ∀ i k, f ((M.simplex i).points k) = g ((M.simplex i).points k)) :
    M.nodalLp hS hM f = M.nodalLp hS hM g := by
  apply Lp.ext
  filter_upwards [M.nodalLp_ae hS hM f,M.nodalLp_ae hS hM g] with x hf hg
  rw [hf,hg,M.nodalFunction_congr h]

theorem nodalLp_add (hS : MeasurableSet S) (hM : M.FaceMatching)
    (f g : SpatialCoordinates d → ℝ) :
    M.nodalLp hS hM (f+g) = M.nodalLp hS hM f + M.nodalLp hS hM g := by
  apply Lp.ext
  filter_upwards [M.nodalLp_ae hS hM (f+g),M.nodalLp_ae hS hM f,
    M.nodalLp_ae hS hM g,Lp.coeFn_add (M.nodalLp hS hM f) (M.nodalLp hS hM g)] with x hfg hf hg ha
  rw [hfg,ha,Pi.add_apply,hf,hg,M.nodalFunction_add]
  rfl

theorem nodalLp_smul (hS : MeasurableSet S) (hM : M.FaceMatching)
    (c : ℝ) (f : SpatialCoordinates d → ℝ) :
    M.nodalLp hS hM (c • f) = c • M.nodalLp hS hM f := by
  apply Lp.ext
  filter_upwards [M.nodalLp_ae hS hM (c • f),M.nodalLp_ae hS hM f,
    Lp.coeFn_smul c (M.nodalLp hS hM f)] with x hcf hf hc
  rw [hcf,hc,Pi.smul_apply,hf,M.nodalFunction_smul]
  rfl

def nodalLpLinearMap (hS : MeasurableSet S) (hM : M.FaceMatching) :
    (SpatialCoordinates d → ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict S) where
  toFun := M.nodalLp hS hM
  map_add' := M.nodalLp_add hS hM
  map_smul' := M.nodalLp_smul hS hM

end Carleman.SimplicialPartition
