module

public import Carleman.Spatial.SimplexNodalInterpolation
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual affine nodal polynomials in L² of a nondegenerate simplex.
The L² map is injective; no L² representative is evaluated at a vertex. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

instance simplexCell_finiteMeasure : IsFiniteMeasure (volume.restrict (simplicialCell T.points)) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using (simplicialCell_compact T.points).measure_lt_top⟩

theorem simplexCell_subset_closure_interior :
    simplicialCell T.points ⊆ closure (interior (simplicialCell T.points)) := by
  rw [(simplicialCell_convex T.points).closure_interior_eq_closure_of_nonempty_interior
    (simplicialCell_interior_nonempty T)]
  exact subset_closure

theorem simplexNodalInterpolant_memLp (c : Fin (d+1) → ℝ) :
    MemLp (simplexNodalInterpolant T c) 2 (volume.restrict (simplicialCell T.points)) := by
  apply MemLp.of_bound (simplexNodalInterpolant T c).continuous_of_finiteDimensional.aestronglyMeasurable ‖c‖
  filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
  exact simplexNodalInterpolant_abs_le T c ‖c‖ (fun i => norm_le_pi_norm c i) hx

def simplexNodalLp (c : Fin (d+1) → ℝ) : Lp ℝ 2 (volume.restrict (simplicialCell T.points)) :=
  (simplexNodalInterpolant_memLp T c).toLp (simplexNodalInterpolant T c)

theorem simplexNodalLp_ae (c : Fin (d+1) → ℝ) :
    simplexNodalLp T c =ᵐ[volume.restrict (simplicialCell T.points)] simplexNodalInterpolant T c :=
  MemLp.coeFn_toLp _

def simplexNodalLpLinear : (Fin (d+1) → ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict (simplicialCell T.points)) where
  toFun := simplexNodalLp T
  map_add' c e := by
    apply Lp.ext
    filter_upwards [simplexNodalLp_ae T (c+e),simplexNodalLp_ae T c,simplexNodalLp_ae T e,
      Lp.coeFn_add (simplexNodalLp T c) (simplexNodalLp T e)] with x h1 h2 h3 h4
    rw [h1,h4,Pi.add_apply,h2,h3]
    simp only [simplexNodalInterpolant_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' r c := by
    change simplexNodalLp T (r • c) = r • simplexNodalLp T c
    apply Lp.ext
    filter_upwards [simplexNodalLp_ae T (r • c),simplexNodalLp_ae T c,
      Lp.coeFn_smul r (simplexNodalLp T c)] with x h1 h2 h3
    rw [h1,h3,Pi.smul_apply,h2]
    simp only [simplexNodalInterpolant_apply,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]

theorem simplexNodalLp_injective : Function.Injective (simplexNodalLp T) := by
  intro c e hce
  have hae : (simplexNodalInterpolant T c : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (simplicialCell T.points)] simplexNodalInterpolant T e :=
    (simplexNodalLp_ae T c).symm.trans (hce ▸ simplexNodalLp_ae T e)
  have heq := Measure.eqOn_of_ae_eq hae (simplexNodalInterpolant T c).continuous_of_finiteDimensional.continuousOn
    (simplexNodalInterpolant T e).continuous_of_finiteDimensional.continuousOn
    (simplexCell_subset_closure_interior T)
  funext i
  have hh := heq (subset_convexHull ℝ _ (Set.mem_range_self i))
  simpa only [simplexNodalInterpolant_vertex] using hh

theorem simplexNodalLp_coefficient_bound : ∃ C > (0:ℝ),
    ∀ c : Fin (d+1) → ℝ, ‖c‖ ≤ C*‖simplexNodalLp T c‖ := by
  obtain ⟨C,hC,hanti⟩ := (simplexNodalLpLinear T).injective_iff_antilipschitz.mp
    (simplexNodalLp_injective T)
  exact ⟨C,hC,fun c => ZeroHomClass.bound_of_antilipschitz (simplexNodalLpLinear T) hanti c⟩

end Carleman
