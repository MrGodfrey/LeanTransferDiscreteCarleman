module

public import Carleman.Spatial.SobolevJet
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Concrete finite affine-coordinate generators in L² on measurable cells.
No Sobolev or boundary assertion is inferred from piecewise affinity alone. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasure ν]

/-- Constant coordinate followed by the actual Euclidean coordinates. -/
def affineCoordinate (k : Fin (d+1)) (x : SpatialCoordinates d) : ℝ :=
  Fin.cases 1 (fun j => x j) k

theorem affineCoordinate_continuous (k : Fin (d+1)) : Continuous (affineCoordinate k) := by
  refine Fin.cases ?_ (fun j => ?_) k
  · exact continuous_const
  · exact PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j

theorem affineCoordinate_bound (k : Fin (d+1)) (x : SpatialCoordinates d) :
    |affineCoordinate k x| ≤ max 1 ‖x‖ := by
  refine Fin.cases ?_ (fun j => ?_) k
  · exact (by norm_num [affineCoordinate])
  · exact (PiLp.norm_apply_le x j).trans (le_max_right _ _)

/-- A genuine L² generator, with its specified polynomial on the cell. -/
def affineCellGenerator (K : Set (SpatialCoordinates d)) (hK : MeasurableSet K)
    (R : ℝ) (hR : ∀ᵐ x ∂ν, x ∈ K → ‖x‖ ≤ R) (k : Fin (d+1)) : Lp ℝ 2 ν :=
  (MemLp.of_bound ((affineCoordinate_continuous k).aestronglyMeasurable.indicator hK)
    (max 1 R) (by
      filter_upwards [hR] with x hx
      by_cases h : x ∈ K
      · rw [Set.indicator_of_mem h,Real.norm_eq_abs]
        exact (affineCoordinate_bound k x).trans (max_le_max le_rfl (hx h))
      · rw [Set.indicator_of_notMem h,norm_zero]
        exact le_trans zero_le_one (le_max_left _ _))).toLp (K.indicator (affineCoordinate k))

theorem affineCellGenerator_ae (K : Set (SpatialCoordinates d)) (hK : MeasurableSet K)
    (R : ℝ) (hR : ∀ᵐ x ∂ν, x ∈ K → ‖x‖ ≤ R) (k : Fin (d+1)) :
    affineCellGenerator K hK R hR k =ᵐ[ν] K.indicator (affineCoordinate k) :=
  MemLp.coeFn_toLp _

variable {ι : Type*} [Fintype ι]
  (K : ι → Set (SpatialCoordinates d)) (hK : ∀ i, MeasurableSet (K i))
  (R : ℝ) (hR : ∀ i, ∀ᵐ x ∂ν, x ∈ K i → ‖x‖ ≤ R)

/-- Finite cellwise affine reconstruction on actual L² equivalence classes. -/
def piecewiseAffineMap : (ι → Fin (d+1) → ℝ) →ₗ[ℝ] Lp ℝ 2 ν where
  toFun c := ∑ i, ∑ k, c i k • affineCellGenerator (K i) (hK i) R (hR i) k
  map_add' c e := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r c := by simp only [Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]; rfl

/-- The representative formula is asserted a.e., as required for L². -/
theorem piecewiseAffineMap_ae (c : ι → Fin (d+1) → ℝ) :
    piecewiseAffineMap K hK R hR c =ᵐ[ν]
      (fun x => ∑ i, ∑ k, c i k * (K i).indicator (affineCoordinate k) x) := by
  have hi (i : ι) : (fun x => (∑ k, c i k • affineCellGenerator (K i) (hK i) R (hR i) k) x) =ᵐ[ν]
      (fun x => ∑ k, c i k * (K i).indicator (affineCoordinate k) x) := by
    apply (Lp.coeFn_finsetSum Finset.univ _).trans
    have hh := eventuallyEq_sum (s := Finset.univ) fun k _ => by
      filter_upwards [Lp.coeFn_smul (c i k) (affineCellGenerator (K i) (hK i) R (hR i) k),
        affineCellGenerator_ae (K i) (hK i) R (hR i) k] with x hx he
      simpa only [Pi.smul_apply,smul_eq_mul,he] using hx
    filter_upwards [hh] with x hx
    simpa only [Finset.sum_apply] using hx
  apply (Lp.coeFn_finsetSum Finset.univ _).trans
  have hh := eventuallyEq_sum (s := Finset.univ) fun i _ => hi i
  filter_upwards [hh] with x hx
  simpa only [Finset.sum_apply] using hx

def piecewiseAffineSpace : Submodule ℝ (Lp ℝ 2 ν) := (piecewiseAffineMap K hK R hR).range

theorem mem_piecewiseAffineSpace_iff (u : Lp ℝ 2 ν) :
    u ∈ piecewiseAffineSpace K hK R hR ↔
      ∃ c : ι → Fin (d+1) → ℝ, u =ᵐ[ν]
        (fun x => ∑ i, ∑ k, c i k * (K i).indicator (affineCoordinate k) x) := by
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨c,piecewiseAffineMap_ae K hK R hR c⟩
  · rintro ⟨c,hc⟩
    exact ⟨c,Lp.ext ((piecewiseAffineMap_ae K hK R hR c).trans hc.symm)⟩

/-- The bound is used only to construct L² representatives; it does not
change the actual space. -/
theorem piecewiseAffineSpace_bound_independent (R' : ℝ)
    (hR' : ∀ i, ∀ᵐ x ∂ν, x ∈ K i → ‖x‖ ≤ R') :
    piecewiseAffineSpace K hK R hR = piecewiseAffineSpace K hK R' hR' := by
  ext u
  rw [mem_piecewiseAffineSpace_iff,mem_piecewiseAffineSpace_iff]

instance piecewiseAffineSpace_finiteDimensional :
    FiniteDimensional ℝ (piecewiseAffineSpace K hK R hR) := by
  unfold piecewiseAffineSpace
  infer_instance

/-- Intersecting with the actual variational space imposes conformity and
boundary conditions separately, while preserving finite dimensionality. -/
def conformingPiecewiseAffineSpace (V : Submodule ℝ (Lp ℝ 2 ν)) : Submodule ℝ (Lp ℝ 2 ν) :=
  piecewiseAffineSpace K hK R hR ⊓ V

instance conformingPiecewiseAffineSpace_finiteDimensional (V : Submodule ℝ (Lp ℝ 2 ν)) :
    FiniteDimensional ℝ (conformingPiecewiseAffineSpace K hK R hR V) :=
  Submodule.finiteDimensional_of_le inf_le_left

theorem conformingPiecewiseAffineSpace_le (V : Submodule ℝ (Lp ℝ 2 ν)) :
    conformingPiecewiseAffineSpace K hK R hR V ≤ V := inf_le_right

end Carleman
