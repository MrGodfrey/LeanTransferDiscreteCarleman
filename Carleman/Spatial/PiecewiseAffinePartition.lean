module

public import Carleman.Spatial.PiecewiseAffineLp

/-! Exact cellwise polynomial characterization for a measurable partition,
up to null sets. Cell boundaries may overlap on a null set. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {ι : Type*} [Fintype ι]
  (K : ι → Set (SpatialCoordinates d))

/-- Actual affine polynomial with the displayed constant and linear part. -/
theorem affineCoordinate_sum (c : Fin (d+1) → ℝ) (x : SpatialCoordinates d) :
    ∑ k, c k*affineCoordinate k x = c 0+∑ j : Fin d, c j.succ*x j := by
  rw [Fin.sum_univ_succ]
  simp only [affineCoordinate,Fin.cases_zero,Fin.cases_succ,mul_one]

theorem piecewiseAffine_formula_on_cell (c : ι → Fin (d+1) → ℝ)
    (x : SpatialCoordinates d) (i : ι) (hi : x ∈ K i)
    (hunique : ∀ j, x ∈ K j → j=i) :
    (∑ j, ∑ k, c j k*(K j).indicator (affineCoordinate k) x) =
      c i 0+∑ k : Fin d, c i k.succ*x k := by
  classical
  rw [Finset.sum_eq_single i]
  · simp only [Set.indicator_of_mem hi]
    exact affineCoordinate_sum _ _
  · intro j _ hji
    have hj : x ∉ K j := fun hj => hji (hunique j hj)
    simp only [Set.indicator_of_notMem hj,mul_zero,Finset.sum_const_zero]
  · simp

variable {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasure ν]
  (hK : ∀ i, MeasurableSet (K i)) (R : ℝ)
  (hR : ∀ i, ∀ᵐ x ∂ν, x ∈ K i → ‖x‖ ≤ R)
  (hpartition : ∀ᵐ x ∂ν, ∃ i, x ∈ K i ∧ ∀ j, x ∈ K j → j=i)

include hpartition in
/-- The finite dimensional range equals all cellwise affine L² states on
an a.e. partition; neither direction assumes finite dimensionality. -/
theorem mem_piecewiseAffineSpace_iff_on_cells (u : Lp ℝ 2 ν) :
    u ∈ piecewiseAffineSpace K hK R hR ↔
      ∀ i, ∃ c : Fin (d+1) → ℝ, ∀ᵐ x ∂ν, x ∈ K i →
        u x = c 0+∑ j : Fin d, c j.succ*x j := by
  rw [mem_piecewiseAffineSpace_iff]
  constructor
  · rintro ⟨c,hc⟩ i
    refine ⟨c i,?_⟩
    filter_upwards [hc,hpartition] with x hx hp
    intro hi
    obtain ⟨j,hj,hunique⟩ := hp
    have he := hunique i hi
    subst j
    exact hx.trans (piecewiseAffine_formula_on_cell K c x i hi hunique)
  · intro H
    choose c hc using H
    refine ⟨c,?_⟩
    have hall : ∀ᵐ x ∂ν, ∀ i, x ∈ K i →
        u x = c i 0+∑ j : Fin d, c i j.succ*x j := (ae_all_iff).mpr hc
    filter_upwards [hall,hpartition] with x hx hp
    obtain ⟨i,hi,hunique⟩ := hp
    exact (hx i hi).trans (piecewiseAffine_formula_on_cell K c x i hi hunique).symm

include hpartition in
/-- Conformity is exact intersection with the original variational subspace. -/
theorem mem_conformingPiecewiseAffineSpace_iff (V : Submodule ℝ (Lp ℝ 2 ν)) (u : Lp ℝ 2 ν) :
    u ∈ conformingPiecewiseAffineSpace K hK R hR V ↔
      u ∈ V ∧ ∀ i, ∃ c : Fin (d+1) → ℝ, ∀ᵐ x ∂ν, x ∈ K i →
        u x = c 0+∑ j : Fin d, c j.succ*x j := by
  change (u ∈ piecewiseAffineSpace K hK R hR ∧ u ∈ V) ↔ _
  rw [mem_piecewiseAffineSpace_iff_on_cells K hK R hR hpartition]
  exact and_comm

end Carleman
