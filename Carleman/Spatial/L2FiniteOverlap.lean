module

public import Carleman.Spatial.SpacetimeWeightedNorm
public import Carleman.Spatial.SubdomainContinuity
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Square summation over actual measurable patches. The upper bound uses
pointwise multiplicity, never the total number of mesh cells. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [Fintype ι] {μ : Measure X}

omit [MeasurableSpace X] in
def finiteCoverMultiplicity (A : ι → Set X) (x : X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => x ∈ A i)).card

omit [MeasurableSpace X] in
theorem sum_indicator_eq_multiplicity (A : ι → Set X) (g : X → ℝ) (x : X) :
    (∑ i, (A i).indicator g x) = (finiteCoverMultiplicity A x:ℝ)*g x := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => x ∈ A i), g x := by
      simp only [Finset.sum_filter, indicator_apply]
    _ = _ := by simp [finiteCoverMultiplicity]

theorem bochnerL2Norm_sq_finite_overlap {f : X → E} (hf : MemLp f 2 μ)
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) (M : ℝ)
    (hoverlap : ∀ᵐ x ∂μ, (finiteCoverMultiplicity A x:ℝ) ≤ M) :
    (∑ i, (bochnerL2Norm (μ.restrict (A i)) f)^2) ≤ M*(bochnerL2Norm μ f)^2 := by
  have hi : Integrable (fun x => ‖f x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hj (i : ι) := hi.indicator (hA i)
  simp_rw [bochnerL2Norm_sq_integral (hf.mono_measure Measure.restrict_le_self)]
  rw [bochnerL2Norm_sq_integral hf, ← integral_const_mul]
  simp_rw [← integral_indicator (hA _)]
  rw [← integral_finsetSum _ (fun i _ => hj i)]
  apply integral_mono_ae (integrable_finsetSum _ (fun i _ => hj i)) (hi.const_mul M)
  filter_upwards [hoverlap] with x hx
  rw [sum_indicator_eq_multiplicity]
  exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

theorem bochnerL2Norm_sq_finite_cover {f : X → E} (hf : MemLp f 2 μ)
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hcover : ∀ᵐ x ∂μ, ∃ i, x ∈ A i) :
    (bochnerL2Norm μ f)^2 ≤ ∑ i, (bochnerL2Norm (μ.restrict (A i)) f)^2 := by
  classical
  have hi : Integrable (fun x => ‖f x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hj (i : ι) := hi.indicator (hA i)
  simp_rw [bochnerL2Norm_sq_integral (hf.mono_measure Measure.restrict_le_self)]
  rw [bochnerL2Norm_sq_integral hf]
  simp_rw [← integral_indicator (hA _)]
  rw [← integral_finsetSum _ (fun i _ => hj i)]
  apply integral_mono_ae hi (integrable_finsetSum _ (fun i _ => hj i))
  filter_upwards [hcover] with x hx
  obtain ⟨i,hi⟩ := hx
  change ‖f x‖^2 ≤ ∑ j : ι, (A j).indicator (fun x => ‖f x‖^2) x
  calc
    _ = (A i).indicator (fun x => ‖f x‖^2) x := by rw [indicator_of_mem hi]
    _ ≤ _ := Finset.single_le_sum (f := fun j : ι => (A j).indicator (fun x => ‖f x‖^2) x) (fun j _ => by
      by_cases hxj : x ∈ A j
      · simp only [indicator_of_mem hxj]; positivity
      · simp only [indicator_of_notMem hxj]; exact le_rfl) (Finset.mem_univ i)

variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

omit [InnerProductSpace ℝ E] in
theorem subdomainLp_norm_eq_bochner (hTS : T ⊆ S) (u : Lp E 2 (volume.restrict S)) :
    ‖subdomainLp hTS u‖ = bochnerL2Norm (volume.restrict T) u := by
  rw [Lp.norm_def,eLpNorm_congr_ae (subdomainLp_ae hTS u)]
  rfl

theorem subdomainLp_sq_finite_overlap (A : ι → Set (SpatialCoordinates d))
    (hA : ∀ i, MeasurableSet (A i)) (hAS : ∀ i, A i ⊆ S) (M : ℝ)
    (hoverlap : ∀ᵐ x ∂volume.restrict S, (finiteCoverMultiplicity A x:ℝ) ≤ M)
    (u : Lp E 2 (volume.restrict S)) :
    (∑ i, ‖subdomainLp (hAS i) u‖^2) ≤ M*‖u‖^2 := by
  have hb := bochnerL2Norm_sq_finite_overlap (Lp.memLp u) A hA M hoverlap
  simp only [Measure.restrict_restrict (hA _),inter_eq_left.mpr (hAS _)] at hb
  simp_rw [subdomainLp_norm_eq_bochner]
  simpa only [bochnerL2Norm,Lp.norm_def] using hb

theorem subdomainLp_sq_finite_cover (A : ι → Set (SpatialCoordinates d))
    (hA : ∀ i, MeasurableSet (A i)) (hAS : ∀ i, A i ⊆ S)
    (hcover : ∀ᵐ x ∂volume.restrict S, ∃ i, x ∈ A i)
    (u : Lp E 2 (volume.restrict S)) :
    ‖u‖^2 ≤ ∑ i, ‖subdomainLp (hAS i) u‖^2 := by
  have hb := bochnerL2Norm_sq_finite_cover (Lp.memLp u) A hA hcover
  simp only [Measure.restrict_restrict (hA _),inter_eq_left.mpr (hAS _)] at hb
  simp_rw [subdomainLp_norm_eq_bochner]
  simpa only [bochnerL2Norm,Lp.norm_def] using hb

end Carleman
