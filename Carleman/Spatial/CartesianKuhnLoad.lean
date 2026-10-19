module

public import Carleman.Spatial.SimplexLoadPolynomial
public import Carleman.Spatial.CartesianKuhnAffineMoment

/-! The actual piecewise affine load uses only interior vertex data.
Shared faces are immaterial for its L² class; the cell formula holds a.e. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianKuhnLoadCoefficients (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) (i : CartesianCellIndex N) (k : Fin (d+1)) : ℝ := by
  classical
  exact if (cartesianFiniteSimplex o δ hδ N i).points k ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)
  then f ((cartesianFiniteSimplex o δ hδ N i).points k) else 0

def cartesianKuhnLoad (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∑ i : CartesianCellIndex N, (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points).indicator
    (simplexLoadPolynomial (cartesianFiniteSimplex o δ hδ N i) (cartesianKuhnLoadCoefficients o δ hδ N f i)) x

theorem cartesianKuhnLoad_on_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) (i : CartesianCellIndex N) :
    cartesianKuhnLoad o δ hδ N f =ᵐ[volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)]
      simplexLoadPolynomial (cartesianFiniteSimplex o δ hδ N i) (cartesianKuhnLoadCoefficients o δ hδ N f i) := by
  let M := cartesianKuhnPartition o δ hδ N
  filter_upwards [(M.ae_partition (openCoordinateBox_isOpen _ _).measurableSet).filter_mono
    (ae_mono (M.cell_measure_le_domain (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) i)),
    ae_restrict_mem (simplicialCell_measurable (cartesianFiniteSimplex o δ hδ N i).points)] with x hx hi
  obtain ⟨j,_,hu⟩ := hx
  have hij := hu i hi
  subst j
  unfold cartesianKuhnLoad
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi _
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (hu j hj)) _
  · simp

theorem cartesianKuhnLoad_memLp (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) :
    MemLp (cartesianKuhnLoad o δ hδ N f) 2 volume := by
  apply memLp_finsetSum
  intro i _
  rw [memLp_indicator_iff_restrict (simplicialCell_measurable _).nullMeasurableSet]
  let T := cartesianFiniteSimplex o δ hδ N i
  let c := cartesianKuhnLoadCoefficients o δ hδ N f i
  have hc := simplexLoadPolynomial_continuous T c
  obtain ⟨B,hB⟩ := (simplicialCell_compact T.points).exists_bound_of_continuousOn hc.continuousOn
  let : IsFiniteMeasure (volume.restrict (simplicialCell T.points)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (simplicialCell_compact T.points).measure_lt_top⟩
  apply MemLp.of_bound hc.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
  exact hB x hx

theorem cartesianKuhnLoad_integrable (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) :
    Integrable (cartesianKuhnLoad o δ hδ N f) volume := by
  apply integrable_finsetSum
  intro i _
  exact ((simplexLoadPolynomial_continuous _ _).continuousOn.integrableOn_compact
    (simplicialCell_compact _)).integrable_indicator (simplicialCell_measurable _)

theorem cartesianKuhnLoad_mul_hat_integrable (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    Integrable (fun x => cartesianKuhnLoad o δ hδ N f x*cartesianKuhnHat o δ hδ N a x) volume := by
  have he : (fun x => cartesianKuhnLoad o δ hδ N f x*cartesianKuhnHat o δ hδ N a x)=
      (fun x => ∑ i : CartesianCellIndex N,
        (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points).indicator
        (fun x => simplexLoadPolynomial (cartesianFiniteSimplex o δ hδ N i)
          (cartesianKuhnLoadCoefficients o δ hδ N f i) x*cartesianKuhnHat o δ hδ N a x) x) := by
    funext x
    simp only [cartesianKuhnLoad,Finset.sum_mul,Set.indicator_mul_left]
  rw [he]
  apply integrable_finsetSum
  intro i _
  exact (((simplexLoadPolynomial_continuous _ _).mul
    (cartesianKuhnHat_continuous o δ hδ N a ha)).continuousOn.integrableOn_compact
      (simplicialCell_compact _)).integrable_indicator (simplicialCell_measurable _)

end Carleman
