module

public import Carleman.Geometry.FiniteHalfspaceFaces
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.MetricSpace.Bounded
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology ContDiff BigOperators
@[expose] public noncomputable section
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def halfspaceExpSum (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) (x : E) : ℝ :=
  ∑ i, Real.exp (((n+1 : ℕ) : ℝ)*(b i-ℓ i x))

def halfspaceSmoothInner (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) : Set E :=
  {x | halfspaceExpSum ℓ b n x < 1/2}

theorem halfspaceExpSum_contDiff (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (halfspaceExpSum ℓ b n) :=
  ContDiff.sum fun i _ => (contDiff_const.mul (contDiff_const.sub (ℓ i).contDiff)).exp

theorem halfspaceExpSum_convex (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) :
    ConvexOn ℝ univ (halfspaceExpSum ℓ b n) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a c ha hc hac
  simp only [halfspaceExpSum,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := convexOn_exp.2 (mem_univ (((n+1:ℕ):ℝ)*(b i-ℓ i x)))
    (mem_univ (((n+1:ℕ):ℝ)*(b i-ℓ i y))) ha hc hac
  simp only [smul_eq_mul] at h
  convert h using 1
  rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
  congr 1
  linear_combination -((n+1:ℕ):ℝ)*(b i)*hac

theorem halfspaceSmoothInner_open (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) :
    IsOpen (halfspaceSmoothInner ℓ b n) :=
  isOpen_lt (halfspaceExpSum_contDiff ℓ b n).continuous continuous_const

theorem halfspaceSmoothInner_convex (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) :
    Convex ℝ (halfspaceSmoothInner ℓ b n) := by
  simpa only [sep_univ,halfspaceSmoothInner] using (halfspaceExpSum_convex ℓ b n).convex_lt (1/2)

theorem halfspaceExpSum_le_half_mem (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    (n : ℕ) {x : E} (hx : halfspaceExpSum ℓ b n x ≤ 1/2) : ∀ i, b i < ℓ i x := by
  classical
  intro i
  have hi : Real.exp (((n+1:ℕ):ℝ)*(b i-ℓ i x)) ≤ halfspaceExpSum ℓ b n x :=
    show Real.exp (((n+1:ℕ):ℝ)*(b i-ℓ i x)) ≤ ∑ j, Real.exp (((n+1:ℕ):ℝ)*(b j-ℓ j x)) from
      Finset.single_le_sum (f := fun j => Real.exp (((n+1:ℕ):ℝ)*(b j-ℓ j x))) (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  have ht : Real.exp (((n+1:ℕ):ℝ)*(b i-ℓ i x)) < 1 := lt_of_le_of_lt (hi.trans hx) (by norm_num)
  have hn : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
  have hp := Real.exp_lt_one_iff.mp ht
  nlinarith

theorem halfspaceSmoothInner_closure_subset (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) :
    closure (halfspaceSmoothInner ℓ b n) ⊆ {x | ∀ i, b i < ℓ i x} := by
  intro x hx
  apply halfspaceExpSum_le_half_mem ℓ b n
  exact closure_minimal (s := halfspaceSmoothInner ℓ b n)
      (fun y hy => (show halfspaceExpSum ℓ b n y < 1/2 from hy).le)
    (isClosed_le (halfspaceExpSum_contDiff ℓ b n).continuous continuous_const) hx

theorem halfspaceSmoothInner_mono (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    Monotone (halfspaceSmoothInner ℓ b) := by
  intro n m hnm x hx
  have hi := halfspaceExpSum_le_half_mem ℓ b n hx.le
  change halfspaceExpSum ℓ b m x < 1/2
  apply lt_of_le_of_lt _ hx
  change (∑ i, Real.exp (((m+1:ℕ):ℝ)*(b i-ℓ i x))) ≤ ∑ i, Real.exp (((n+1:ℕ):ℝ)*(b i-ℓ i x))
  apply Finset.sum_le_sum
  intro i _
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_right (by exact_mod_cast Nat.add_le_add_right hnm 1) (sub_nonpos.mpr (hi i).le)

theorem halfspaceExpSum_tendsto_zero (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    {x : E} (hx : ∀ i, b i < ℓ i x) :
    Tendsto (fun n => halfspaceExpSum ℓ b n x) atTop (𝓝 0) := by
  have ht (i : ι) : Tendsto (fun n : ℕ => Real.exp (((n+1:ℕ):ℝ)*(b i-ℓ i x))) atTop (𝓝 0) := by
    simp_rw [Real.exp_nat_mul]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (sub_neg.mpr (hx i)))).comp (tendsto_add_atTop_nat 1)
  simpa only [halfspaceExpSum,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => ht i)

theorem halfspaceSmoothInner_eventually_mem (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    {x : E} (hx : ∀ i, b i < ℓ i x) :
    ∀ᶠ n in atTop, x ∈ halfspaceSmoothInner ℓ b n :=
  (halfspaceExpSum_tendsto_zero ℓ b hx).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))

theorem halfspaceSmoothInner_exhaustion (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    ⋃ n, halfspaceSmoothInner ℓ b n = {x | ∀ i, b i < ℓ i x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact halfspaceExpSum_le_half_mem ℓ b n hn.le
  · intro hx
    obtain ⟨n,hn⟩ := (halfspaceSmoothInner_eventually_mem ℓ b hx).exists
    exact mem_iUnion.mpr ⟨n,hn⟩

theorem halfspaceSmoothInner_compact [ProperSpace E]
    (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i < ℓ i x}) (n : ℕ) :
    IsCompact (closure (halfspaceSmoothInner ℓ b n)) :=
  isCompact_of_isClosed_isBounded isClosed_closure (hb.subset (halfspaceSmoothInner_closure_subset ℓ b n))

theorem halfspaceExpSum_hasFDerivAt (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) (x : E) :
    HasFDerivAt (halfspaceExpSum ℓ b n)
      (∑ i, Real.exp (((n+1:ℕ):ℝ)*(b i-ℓ i x)) • (-((n+1:ℕ):ℝ) • ℓ i)) x := by
  apply HasFDerivAt.fun_sum
  intro i _
  convert (((ℓ i).hasFDerivAt.const_sub (b i)).const_mul ((n+1:ℕ):ℝ)).exp using 1
  ext z
  simp only [smul_apply,smul_eq_mul,neg_apply]
  ring

theorem halfspaceExpSum_support (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ) (x y : E) :
    halfspaceExpSum ℓ b n x + fderiv ℝ (halfspaceExpSum ℓ b n) x (y-x) ≤
      halfspaceExpSum ℓ b n y := by
  rw [(halfspaceExpSum_hasFDerivAt ℓ b n x).fderiv]
  simp only [halfspaceExpSum,sum_apply,smul_apply,
    smul_eq_mul,map_sub]
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (((n+1:ℕ):ℝ)*(ℓ i x-ℓ i y)))
    (Real.exp_pos (((n+1:ℕ):ℝ)*(b i-ℓ i x))).le
  rw [← Real.exp_add] at he
  convert he using 1 <;> congr 1 <;> ring

theorem halfspaceSmoothInner_boundary_regular (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    (n : ℕ) {c : E} (hc : c ∈ halfspaceSmoothInner ℓ b n)
    {x : E} (hx : x ∈ frontier (halfspaceSmoothInner ℓ b n)) :
    halfspaceExpSum ℓ b n x=1/2 ∧ fderiv ℝ (halfspaceExpSum ℓ b n) x ≠ 0 := by
  have hle : halfspaceExpSum ℓ b n x ≤ 1/2 :=
    closure_minimal (s := halfspaceSmoothInner ℓ b n)
      (fun y hy => (show halfspaceExpSum ℓ b n y < 1/2 from hy).le)
      (isClosed_le (halfspaceExpSum_contDiff ℓ b n).continuous continuous_const) hx.1
  have hnot : ¬halfspaceExpSum ℓ b n x < 1/2 := by
    have h := hx.2
    rw [(halfspaceSmoothInner_open ℓ b n).interior_eq] at h
    exact h
  have he : halfspaceExpSum ℓ b n x=1/2 := le_antisymm hle (not_lt.mp hnot)
  refine ⟨he,?_⟩
  intro hz
  have hs := halfspaceExpSum_support ℓ b n x c
  rw [hz,zero_apply,add_zero,he] at hs
  exact (not_lt_of_ge hs) hc


theorem exists_halfspace_smooth_exhaustion [ProperSpace E]
    (ℓ : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (c : E) (hc : ∀ i, b i < ℓ i c)
    (hb : Bornology.IsBounded {x | ∀ i, b i < ℓ i x}) :
    ∃ g : ℕ → E → ℝ, ∃ U : ℕ → Set E,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, ConvexOn ℝ univ (g n)) ∧
      (∀ n, U n={x | g n x < 1/2}) ∧
      (∀ n, IsOpen (U n)) ∧ (∀ n, Convex ℝ (U n)) ∧
      (∀ n, c ∈ U n) ∧ Monotone U ∧
      (∀ n, IsCompact (closure (U n))) ∧
      (∀ n, closure (U n) ⊆ {x | ∀ i, b i < ℓ i x}) ∧
      (⋃ n, U n)={x | ∀ i, b i < ℓ i x} ∧
      (∀ n x, x ∈ frontier (U n) → g n x=1/2 ∧ fderiv ℝ (g n) x ≠ 0) := by
  obtain ⟨N,hN⟩ := (halfspaceSmoothInner_eventually_mem ℓ b hc).exists
  let U := fun n => halfspaceSmoothInner ℓ b (N+n)
  have hcU (n : ℕ) : c ∈ U n := halfspaceSmoothInner_mono ℓ b (Nat.le_add_right N n) hN
  have hm : Monotone U := fun n m hnm => halfspaceSmoothInner_mono ℓ b (Nat.add_le_add_left hnm N)
  refine ⟨(fun n => halfspaceExpSum ℓ b (N+n)),U,
    (fun n => halfspaceExpSum_contDiff ℓ b (N+n)),
    (fun n => halfspaceExpSum_convex ℓ b (N+n)),(fun n => rfl),
    (fun n => halfspaceSmoothInner_open ℓ b (N+n)),
    (fun n => halfspaceSmoothInner_convex ℓ b (N+n)),hcU,hm,
    (fun n => halfspaceSmoothInner_compact ℓ b hb (N+n)),
    (fun n => halfspaceSmoothInner_closure_subset ℓ b (N+n)),?_,?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨n,hn⟩ := mem_iUnion.mp hx
      exact halfspaceExpSum_le_half_mem ℓ b (N+n) hn.le
    · intro hx
      obtain ⟨n,hn⟩ := (halfspaceSmoothInner_eventually_mem ℓ b hx).exists
      exact mem_iUnion.mpr ⟨n,halfspaceSmoothInner_mono ℓ b (Nat.le_add_left n N) hn⟩
  · intro n x hx
    exact halfspaceSmoothInner_boundary_regular ℓ b (N+n) (hcU n) hx

end Carleman
