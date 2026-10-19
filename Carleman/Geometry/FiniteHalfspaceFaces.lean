module

public import Carleman.Geometry.FiniteHalfspaceCharts

/-! Actual flat faces of a finite strict halfspace intersection. -/
@[expose] public noncomputable section
open Set Metric
open scoped Topology
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem finite_halfspace_mem_closure (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    (c : E) (hc : ∀ i, b i < ℓ i c) (y : E) (hy : ∀ i, b i ≤ ℓ i y) :
    y ∈ closure {x | ∀ i, b i < ℓ i x} := by
  let f : ℝ → E := fun t => (1-t) • y+t • c
  have hf : Continuous f :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have h0 : (0:ℝ) ∈ closure (Ioo (0:ℝ) 1) := by
    rw [closure_Ioo (by norm_num)]
    exact ⟨le_rfl,by norm_num⟩
  have hm : MapsTo f (Ioo (0:ℝ) 1) {x | ∀ i, b i < ℓ i x} := by
    intro t ht i
    dsimp only [f]
    rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
    have h1 := mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) (sub_nonneg.mpr (hy i))
    have h2 := mul_pos ht.1 (sub_pos.mpr (hc i))
    nlinarith
  have h := hf.continuousWithinAt.mem_closure h0 hm
  simpa only [f,sub_zero,one_smul,zero_smul,add_zero] using h

omit [Fintype ι] in
theorem finite_halfspace_closure_iff (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    (c : E) (hc : ∀ i, b i < ℓ i c) (y : E) :
    y ∈ closure {x | ∀ i, b i < ℓ i x} ↔ ∀ i, b i ≤ ℓ i y := by
  constructor
  · intro hy i
    exact closure_minimal (fun x hx => (hx i).le)
      (isClosed_le continuous_const (ℓ i).continuous) hy
  · exact finite_halfspace_mem_closure ℓ b c hc y

theorem finite_halfspace_face_neighborhood (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    (c : E) (hc : ∀ i, b i < ℓ i c) (j : ι) (x : E)
    (hj : ℓ j x=b j) (hother : ∀ i, i ≠ j → b i < ℓ i x) :
    ∃ r : ℝ, 0 < r ∧ ∀ y, ‖y-x‖ < r → ℓ j (y-x)=0 →
      y ∈ frontier {z | ∀ i, b i < ℓ i z} := by
  classical
  let U : Set E := {y | ∀ i, i ≠ j → b i < ℓ i y}
  have hU : IsOpen U := by
    have he : U=⋂ i, {y | i ≠ j → b i < ℓ i y} := by ext y; simp [U]
    rw [he]
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : i=j
    · simp only [hi,ne_eq,not_true_eq_false,false_implies,ofPred_true]
      exact isOpen_univ
    · simpa only [hi,ne_eq,not_false_eq_true,true_implies] using
        isOpen_lt (continuous_const : Continuous (fun _ : E => b i)) (ℓ i).continuous
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU x hother
  refine ⟨r,hr,?_⟩
  intro y hy hplane
  have hyU := hball (show y ∈ Metric.ball x r by simpa only [Metric.mem_ball,dist_eq_norm] using hy)
  have hyj : ℓ j y=b j := by rw [map_sub,hj] at hplane; linarith
  have hyle : ∀ i, b i ≤ ℓ i y := by
    intro i
    by_cases hi : i=j
    · simpa only [hi,hyj] using le_rfl (a := b j)
    · exact (hyU i hi).le
  refine ⟨finite_halfspace_mem_closure ℓ b c hc y hyle,?_⟩
  intro hmem
  have hs := interior_subset hmem
  have hbad := hs j
  linarith

omit [Fintype ι] in
theorem finite_halfspace_face_mem_closure (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    (j : ι) (w : E) (hw : ℓ j w=b j) (hwi : ∀ i, i ≠ j → b i < ℓ i w)
    (x : E) (hx : ℓ j x=b j) (hxi : ∀ i, b i ≤ ℓ i x) :
    x ∈ closure {y | ℓ j y=b j ∧ ∀ i, i ≠ j → b i < ℓ i y} := by
  let f : ℝ → E := fun t => (1-t) • x+t • w
  have hf : Continuous f :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have h0 : (0:ℝ) ∈ closure (Ioo (0:ℝ) 1) := by
    rw [closure_Ioo (by norm_num)]
    exact ⟨le_rfl,by norm_num⟩
  have hm : MapsTo f (Ioo (0:ℝ) 1)
      {y | ℓ j y=b j ∧ ∀ i, i ≠ j → b i < ℓ i y} := by
    intro t ht
    constructor
    · dsimp only [f]
      rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,hx,hw]
      ring
    · intro i hi
      dsimp only [f]
      rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      have h1 := mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) (sub_nonneg.mpr (hxi i))
      have h2 := mul_pos ht.1 (sub_pos.mpr (hwi i hi))
      nlinarith
  have h := hf.continuousWithinAt.mem_closure h0 hm
  simpa only [f,sub_zero,one_smul,zero_smul,add_zero] using h

end Carleman
