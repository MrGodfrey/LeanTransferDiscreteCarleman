module

public import Carleman.Geometry.DirectionalCoordinates
public import Carleman.Geometry.LocalLipschitzCharts
public import Mathlib.Data.Finset.Lattice.Fold

/-! Actual boundary graph charts for finite strict halfspace intersections
with a strict interior point. Active faces produce a finite maximum of linear
functions; inactive faces stay strict on a genuine neighborhood. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open Set Metric
open scoped NNReal
namespace Carleman

theorem finite_linear_max_lipschitz {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Finset ι) (hs : s.Nonempty) (g : ι → F →L[ℝ] ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K (fun y => s.sup' hs (fun i => g i y)) := by
  classical
  let K := s.sup (fun i => ‖g i‖₊)
  refine ⟨K,LipschitzWith.of_le_add_mul K ?_⟩
  intro x y
  apply Finset.sup'_le
  intro i hi
  have hK : ‖g i‖₊ ≤ K := Finset.le_sup (f := fun j => ‖g j‖₊) hi
  have hlip := ((g i).lipschitzWith.weaken hK).le_add_mul x y
  exact hlip.trans (add_le_add (Finset.le_sup' (fun j => g j y) hi) le_rfl)

theorem finite_halfspace_graph_charts {d : ℕ} {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates (d+1) →L[ℝ] ℝ) (b : ι → ℝ)
    (x₀ : SpatialCoordinates (d+1)) (hx₀ : ∀ i, b i < ℓ i x₀) :
    HasLipschitzGraphCharts {x | ∀ i, b i < ℓ i x} (SpatialCoordinates d) := by
  classical
  let S : Set (SpatialCoordinates (d+1)) := {x | ∀ i, b i < ℓ i x}
  have hS : IsOpen S := by
    have he : S=⋂ i, {x | b i < ℓ i x} := by ext x; simp [S]
    rw [he]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (ℓ i).continuous
  intro c hc
  change c ∈ frontier S at hc
  have hcnot : c ∉ S := by
    simpa only [hS.interior_eq] using hc.2
  have hcle (i : ι) : b i ≤ ℓ i c :=
    closure_minimal (fun x hx => (hx i).le)
      (isClosed_le continuous_const (ℓ i).continuous) hc.1
  let s : Finset ι := Finset.univ.filter (fun i => b i=ℓ i c)
  have hs : s.Nonempty := by
    by_contra! hn
    apply hcnot
    intro i
    exact lt_of_le_of_ne (hcle i) (by
      intro he
      have himem : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i,he⟩
      rw [hn] at himem
      simp at himem)
  let v := x₀-c
  have hv : v ≠ 0 := by
    intro he
    have he' : x₀=c := sub_eq_zero.mp he
    apply hcnot
    change ∀ i, b i < ℓ i c
    rwa [← he']
  obtain ⟨e,hev⟩ := exists_directional_coordinates v hv
  let g : ι → SpatialCoordinates d →L[ℝ] ℝ := fun i =>
    (-((ℓ i v)⁻¹)) • ((ℓ i).comp (e.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (SpatialCoordinates d) ℝ)))
  obtain ⟨K,hK⟩ := finite_linear_max_lipschitz s hs g
  let U : Set (SpatialCoordinates (d+1)) := {x | ∀ i, b i ≠ ℓ i c → b i < ℓ i x}
  have hU : IsOpen U := by
    have he : U=⋂ i, {x | b i ≠ ℓ i c → b i < ℓ i x} := by ext x; simp [U]
    rw [he]
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : b i=ℓ i c
    · simp only [hi,ne_eq,not_true_eq_false,false_implies,ofPred_true]
      exact isOpen_univ
    · simpa only [ne_eq,hi,not_false_eq_true,true_implies] using
        isOpen_lt (continuous_const : Continuous (fun _ : SpatialCoordinates (d+1) => b i))
          (ℓ i).continuous
  have hcU : c ∈ U := fun i hi => lt_of_le_of_ne (hcle i) hi
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hU c hcU
  refine ⟨R,hR,e,K,(fun y => s.sup' hs (fun i => g i y)),hK,?_⟩
  intro x hx
  have hdecomp : x-c=e.symm ((e (x-c)).1,0)+(e (x-c)).2 • v := by
    apply e.injective
    rw [map_add,map_smul,e.apply_symm_apply,hev]
    ext <;> simp
  have hactive (i : ι) (hi : i ∈ s) :
      b i < ℓ i x ↔ g i (e (x-c)).1 < (e (x-c)).2 := by
    have hi' := (Finset.mem_filter.mp hi).2
    have hvi : 0 < ℓ i v := by
      dsimp only [v]
      rw [map_sub]
      linarith [hx₀ i]
    have hgi (y : SpatialCoordinates d) : g i y= -ℓ i (e.symm (y,0))/ℓ i v := by
      simp only [g,smul_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe,ContinuousLinearMap.inl_apply,smul_eq_mul,div_eq_mul_inv]
      ring
    have he := congrArg (fun z => ℓ i z) hdecomp
    rw [map_sub,map_add,map_smul,smul_eq_mul] at he
    rw [hgi,div_lt_iff₀ hvi]
    change b i < ℓ i x ↔ -ℓ i (e.symm ((e (x-c)).1,0)) < (e (x-c)).2*ℓ i v
    constructor <;> intro hx' <;> linarith
  rw [Finset.sup'_lt_iff]
  constructor
  · intro h i hi
    exact (hactive i hi).mp (h i)
  · intro h i
    by_cases hi : b i=ℓ i c
    · have his : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
      exact (hactive i his).mpr (h i his)
    · exact hball hx i hi

theorem finite_halfspace_bounded_lipschitz {d : ℕ} {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates (d+1) →L[ℝ] ℝ) (b : ι → ℝ)
    (x₀ : SpatialCoordinates (d+1)) (hx₀ : ∀ i, b i < ℓ i x₀)
    (hb : Bornology.IsBounded {x | ∀ i, b i < ℓ i x}) :
    IsBoundedLipschitzDomain {x | ∀ i, b i < ℓ i x} (SpatialCoordinates d) := by
  apply boundedLipschitz_iff_global_graph_charts.mpr
  refine ⟨?_,hb,finite_halfspace_graph_charts ℓ b x₀ hx₀⟩
  have he : {x | ∀ i, b i < ℓ i x}=⋂ i, {x | b i < ℓ i x} := by ext x; simp
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (ℓ i).continuous

end Carleman
