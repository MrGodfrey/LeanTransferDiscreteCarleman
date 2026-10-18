module

public import Carleman.Spatial.SimplicialNodalGluing

/-! The actual continuous nodal function as an L² class, with exact piecewise
polynomial membership. Sobolev/Dirichlet membership is not asserted here. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def affinePolynomialCoefficients (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) : Fin (d+1) → ℝ :=
  Fin.cases (p 0) (fun j => p.linear (EuclideanSpace.basisFun (Fin d) ℝ j))

theorem affinePolynomialCoefficients_apply (p : SpatialCoordinates d →ᵃ[ℝ] ℝ)
    (x : SpatialCoordinates d) :
    p x = affinePolynomialCoefficients p 0 +
      ∑ j : Fin d, affinePolynomialCoefficients p j.succ*x j := by
  have hl := congrArg p.linear ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x)
  simp only [map_sum,map_smul,EuclideanSpace.basisFun_repr,smul_eq_mul] at hl
  have hp := p.map_vadd (0 : SpatialCoordinates d) x
  simp only [vadd_eq_add,add_zero] at hp
  rw [hp,← hl]
  simp only [affinePolynomialCoefficients,Fin.cases_zero,Fin.cases_succ,mul_comm,add_comm]

namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def nodalBound (f : SpatialCoordinates d → ℝ) : ℝ :=
  ∑ i, ∑ k, |f ((M.simplex i).points k)|

theorem nodalBound_nonneg (f : SpatialCoordinates d → ℝ) : 0 ≤ M.nodalBound f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem nodalBound_vertex (f : SpatialCoordinates d → ℝ) (i : ι) (k : Fin (d+1)) :
    |f ((M.simplex i).points k)| ≤ M.nodalBound f :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (f ((M.simplex i).points j)))
    (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg (f ((M.simplex j).points k)))
        (Finset.mem_univ i))

/-- This coarse finite bound is used only for L² existence; the local
interpolation stability constant remains one. -/
theorem nodalFunction_bound (hM : M.FaceMatching) (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) : |M.nodalFunction f x| ≤ M.nodalBound f := by
  classical
  by_cases hx : ∃ i, x ∈ M.cell i
  · obtain ⟨i,hi⟩ := hx
    rw [M.nodalFunction_on_cell hM f i hi]
    exact simplexNodalInterpolant_abs_le _ _ _ (M.nodalBound_vertex f i) hi
  · rw [nodalFunction,dite_eq_right hx,abs_zero]
    exact M.nodalBound_nonneg f

variable [IsFiniteMeasure (volume.restrict S)]

theorem nodalFunction_memLp (hS : MeasurableSet S) (hM : M.FaceMatching)
    (f : SpatialCoordinates d → ℝ) : MemLp (M.nodalFunction f) 2 (volume.restrict S) :=
  MemLp.of_bound (((M.nodalFunction_continuousOn hM f).mono subset_closure).aestronglyMeasurable hS)
    (M.nodalBound f) (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using M.nodalFunction_bound hM f x)

def nodalLp (hS : MeasurableSet S) (hM : M.FaceMatching)
    (f : SpatialCoordinates d → ℝ) : Lp ℝ 2 (volume.restrict S) :=
  (M.nodalFunction_memLp hS hM f).toLp (M.nodalFunction f)

theorem nodalLp_ae (hS : MeasurableSet S) (hM : M.FaceMatching) (f : SpatialCoordinates d → ℝ) :
    M.nodalLp hS hM f =ᵐ[volume.restrict S] M.nodalFunction f := MemLp.coeFn_toLp _

theorem nodalLp_piecewise_affine (hS : MeasurableSet S) (hM : M.FaceMatching)
    (f : SpatialCoordinates d → ℝ) :
    M.nodalLp hS hM f ∈ piecewiseAffineSpace M.cell (fun _ => simplicialCell_measurable _)
      (simplicialRadius fun i => (M.simplex i).points)
      (fun i => Filter.Eventually.of_forall fun _ hx => simplicialCell_norm_le _ i hx) := by
  rw [mem_piecewiseAffineSpace_iff_on_cells _ _ _ _ (M.ae_partition hS)]
  intro i
  refine ⟨affinePolynomialCoefficients (M.localNodal f i),?_⟩
  filter_upwards [M.nodalLp_ae hS hM f] with x hx
  intro hi
  rw [hx,M.nodalFunction_on_cell hM f i hi]
  exact affinePolynomialCoefficients_apply _ _

end SimplicialPartition
end Carleman
