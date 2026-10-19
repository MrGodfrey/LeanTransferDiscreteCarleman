module

public import Carleman.Geometry.AffineSimplexInball
public import Carleman.Geometry.KuhnInverseMap
public import Carleman.Geometry.KuhnAllowedWeightComparison
public import Carleman.Spatial.SimplicialDiameter

/-! Actual uniform inballs and diameters for the physical Cartesian Kuhn
partition. These supply the shape hypotheses of the nodal estimates. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhn_cellDiameter_le (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (h : ℝ) (hh : 0 < h) (hstep : ∀ j, δ j ≤ h)
    (i : CartesianCellIndex N) :
    (cartesianKuhnPartition o δ hδ N).cellDiameter i ≤ (d+1:ℝ)*h := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  exact (cartesianKuhnSimplex_dist_le o δ hδ _ i.2 h hh hstep hx hy).trans
    (by nlinarith)

theorem cartesianKuhn_maxDiameter_le (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (h : ℝ) (hh : 0 < h) (hstep : ∀ j, δ j ≤ h) :
    (cartesianKuhnPartition o δ hδ N).maxDiameter ≤ (d+1:ℝ)*h := by
  let D : CartesianCellIndex N → NNReal := fun i =>
    ⟨(cartesianKuhnPartition o δ hδ N).cellDiameter i,
      (cartesianKuhnPartition o δ hδ N).cellDiameter_nonneg i⟩
  have hD : Finset.univ.sup D ≤ (⟨(d+1:ℝ)*h,by positivity⟩ : NNReal) := by
    apply Finset.sup_le
    intro i _
    exact cartesianKuhn_cellDiameter_le o δ hδ N h hh hstep i
  exact hD

theorem cartesianKuhn_uniform_inballs (κ : ℝ) (hκ : 0 < κ) :
    ∃ C > (0:ℝ), ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (h : ℝ), 0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
      ∃ (a : CartesianCellIndex N → SpatialCoordinates d) (r : ℝ), 0 < r ∧
        (∀ i, Metric.ball (a i) r ⊆ (cartesianKuhnPartition o δ hδ N).cell i) ∧
        (∀ i, (cartesianKuhnPartition o δ hδ N).cellDiameter i ≤ C*r) := by
  obtain ⟨a₀,r₀,hr₀,hball⟩ := simplex_exists_inball (kuhnReferenceSimplex d)
  refine ⟨(d+1:ℝ)*κ/r₀,by positivity,?_⟩
  intro o δ hδ N h hh hlower hupper
  let a : CartesianCellIndex N → SpatialCoordinates d := fun i =>
    affineChange ((coordinatePermutation i.2).trans (coordinateDilation δ hδ))
      (cartesianGridPoint o δ (cartesianCellLatticeIndex N i).1) a₀
  refine ⟨a,r₀*h/κ,by positivity,?_,?_⟩
  · intro i
    have hi := affineSimplex_contains_ball (kuhnReferenceSimplex d) a₀ r₀ hball
      ((coordinatePermutation i.2).trans (coordinateDilation δ hδ))
      (cartesianGridPoint o δ (cartesianCellLatticeIndex N i).1) (κ/h) (div_pos hκ hh)
      (cartesianKuhn_inverse_map_bound δ hδ i.2 κ h hκ hh hlower)
    have he : r₀/(κ/h)=r₀*h/κ := by field_simp
    rw [he] at hi
    exact hi
  · intro i
    have he : (d+1:ℝ)*κ/r₀*(r₀*h/κ)=(d+1:ℝ)*h := by field_simp
    rw [he]
    exact cartesianKuhn_cellDiameter_le o δ hδ N h hh hupper i

end Carleman
