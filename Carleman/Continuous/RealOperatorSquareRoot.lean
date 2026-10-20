module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.MetricSpace.Cauchy
/-! A norm-convergent real Banach algebra iteration constructs positive square roots
on arbitrary real Hilbert spaces, without a complex functional-calculus assumption. -/
@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace Carleman

def sqrtScalarIter : ℕ → ℝ
  | 0 => 0
  | n+1 => (1+(sqrtScalarIter n)^2)/2

theorem sqrtScalarIter_bounds (n : ℕ) : 0 ≤ sqrtScalarIter n ∧ sqrtScalarIter n ≤ 1 := by
  induction n with
  | zero => norm_num [sqrtScalarIter]
  | succ n ih =>
    simp only [sqrtScalarIter]
    constructor <;> nlinarith [sq_nonneg (sqrtScalarIter n)]

theorem sqrtScalarIter_monotone : Monotone sqrtScalarIter := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [sqrtScalarIter]
  nlinarith [sq_nonneg (sqrtScalarIter n-1)]

theorem sqrtScalarIter_tendsto : Tendsto sqrtScalarIter atTop (𝓝 1) := by
  have hb : BddAbove (range sqrtScalarIter) := ⟨1,by rintro _ ⟨n,rfl⟩; exact (sqrtScalarIter_bounds n).2⟩
  have ht := tendsto_atTop_ciSup sqrtScalarIter_monotone hb
  have hs : Tendsto (fun n => sqrtScalarIter (n+1)) atTop (𝓝 (⨆ n, sqrtScalarIter n)) :=
    ht.comp (tendsto_add_atTop_nat 1)
  have he : (⨆ n, sqrtScalarIter n)=(1+(⨆ n, sqrtScalarIter n)^2)/2 :=
    tendsto_nhds_unique hs ((tendsto_const_nhds.add (ht.pow 2)).div_const 2)
  have hlim : (⨆ n, sqrtScalarIter n)=1 := by nlinarith [sq_nonneg ((⨆ n, sqrtScalarIter n)-1)]
  rwa [hlim] at ht

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def sqrtComplementIter (X : A) : ℕ → A
  | 0 => 0
  | n+1 => (1/2:ℝ) • (X+sqrtComplementIter X n*sqrtComplementIter X n)

theorem sqrtComplementIter_norm (X : A) (hX : ‖X‖ ≤ 1) (n : ℕ) :
    ‖sqrtComplementIter X n‖ ≤ sqrtScalarIter n := by
  induction n with
  | zero => simp [sqrtComplementIter,sqrtScalarIter]
  | succ n ih =>
    simp only [sqrtComplementIter,sqrtScalarIter,norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hc := sqrtScalarIter_bounds n
    have hm := norm_mul_le (sqrtComplementIter X n) (sqrtComplementIter X n)
    have ha := norm_add_le X (sqrtComplementIter X n*sqrtComplementIter X n)
    have hh := mul_self_le_mul_self (norm_nonneg _) ih
    nlinarith

theorem sqrtComplementIter_dist (X : A) (hX : ‖X‖ ≤ 1) (n m : ℕ) :
    ‖sqrtComplementIter X n-sqrtComplementIter X m‖ ≤ |sqrtScalarIter n-sqrtScalarIter m| := by
  induction n generalizing m with
  | zero => simpa only [sqrtComplementIter,sqrtScalarIter,zero_sub,norm_neg,abs_neg,abs_of_nonneg (sqrtScalarIter_bounds m).1] using sqrtComplementIter_norm X hX m
  | succ n ih =>
    cases m with
    | zero =>
      change ‖sqrtComplementIter X (n+1)-0‖ ≤ |sqrtScalarIter (n+1)-0|
      rw [sub_zero,sub_zero,abs_of_nonneg (sqrtScalarIter_bounds (n+1)).1]
      exact sqrtComplementIter_norm X hX (n+1)
    | succ m =>
      let p := sqrtComplementIter X n
      let r := sqrtComplementIter X m
      let c := sqrtScalarIter n
      let e := sqrtScalarIter m
      have hn := sqrtComplementIter_norm X hX n
      have hm := sqrtComplementIter_norm X hX m
      have hc := (sqrtScalarIter_bounds n).1
      have he := (sqrtScalarIter_bounds m).1
      have hd : ‖p-r‖ ≤ |c-e| := ih m
      have hi : sqrtComplementIter X (n+1)-sqrtComplementIter X (m+1)=
          (1/2:ℝ) • (p*(p-r)+(p-r)*r) := by
        simp only [sqrtComplementIter,←smul_sub]
        congr 1
        dsimp [p,r]
        noncomm_ring
      rw [hi,norm_smul]
      have ha : sqrtScalarIter (n+1)-sqrtScalarIter (m+1)=(1/2:ℝ)*(c+e)*(c-e) := by
        dsimp [sqrtScalarIter,c,e]
        ring
      rw [ha,abs_mul,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/2),
        abs_of_nonneg (add_nonneg hc he)]
      have hnorm : ‖p*(p-r)+(p-r)*r‖ ≤ (c+e)*|c-e| := calc
        _ ≤ ‖p*(p-r)‖+‖(p-r)*r‖ := norm_add_le _ _
        _ ≤ ‖p‖*‖p-r‖+‖p-r‖*‖r‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ c*|c-e|+|c-e| * e := add_le_add
          (mul_le_mul hn hd (norm_nonneg _) hc)
          (mul_le_mul hd hm (norm_nonneg _) (abs_nonneg _))
        _ = (c+e)*|c-e| := by ring
      norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      nlinarith

theorem sqrtComplementIter_cauchy (X : A) (hX : ‖X‖ ≤ 1) : CauchySeq (sqrtComplementIter X) := by
  apply cauchySeq_of_le_tendsto_0' (fun n => 1-sqrtScalarIter n)
  · intro n m hnm
    rw [dist_eq_norm]
    have hh := sqrtComplementIter_dist X hX n m
    rw [abs_of_nonpos (sub_nonpos.mpr (sqrtScalarIter_monotone hnm))] at hh
    linarith [(sqrtScalarIter_bounds m).2]
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub sqrtScalarIter_tendsto

variable [CompleteSpace A]

theorem sqrtComplementIter_exists_limit (X : A) (hX : ‖X‖ ≤ 1) :
    ∃ P : A, Tendsto (sqrtComplementIter X) atTop (𝓝 P) ∧ ‖P‖ ≤ 1 ∧
      P=(1/2:ℝ) • (X+P*P) := by
  obtain ⟨P,hP⟩ := cauchySeq_tendsto_of_complete (sqrtComplementIter_cauchy X hX)
  refine ⟨P,hP,?_,?_⟩
  · exact le_of_tendsto_of_tendsto hP.norm sqrtScalarIter_tendsto
      (Filter.Eventually.of_forall (sqrtComplementIter_norm X hX))
  · have hs : Tendsto (fun n => sqrtComplementIter X (n+1)) atTop (𝓝 P) :=
      hP.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hs ((tendsto_const_nhds.add (hP.mul hP)).const_smul (1/2:ℝ))

omit [CompleteSpace A] in
theorem sqrtComplementIter_limit_square (X P : A)
    (hP : P=(1/2:ℝ) • (X+P*P)) : (1-P)*(1-P)=1-X := by
  have htwo := congrArg (fun z : A => (2:ℝ) • z) hP
  have he : P+P=X+P*P := by
    simpa only [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul,two_smul] using htwo
  calc
    _ = 1-(P+P)+P*P := by noncomm_ring
    _ = 1-X := by rw [he]; abel


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem sqrtComplementIter_selfAdjoint (X : H →L[ℝ] H) (hX : IsSelfAdjoint X) (n : ℕ) :
    IsSelfAdjoint (sqrtComplementIter X n) := by
  induction n with
  | zero => exact IsSelfAdjoint.zero _
  | succ n ih =>
    exact (IsSelfAdjoint.all (1/2:ℝ)).smul (hX.add (by simpa only [pow_two] using ih.pow 2))

theorem positive_contraction_complement_norm (R : H →L[ℝ] H)
    (hR : R.IsPositive) (hn : ‖R‖ ≤ 1) : ‖1-R‖ ≤ 1 := by
  have hs : (1-R).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ((IsSelfAdjoint.one (H →L[ℝ] H)).sub hR.isSelfAdjoint)
  rw [(1-R).norm_eq_iSup_rayleighQuotient hs]
  apply ciSup_le
  intro x
  have hi := hR.inner_nonneg_left x
  have hu : inner ℝ (R x) x ≤ ‖x‖^2 := calc
    _ ≤ ‖R x‖*‖x‖ := (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    _ ≤ ‖x‖*‖x‖ := mul_le_mul_of_nonneg_right
      ((R.le_opNorm x).trans (by nlinarith [norm_nonneg x])) (norm_nonneg x)
    _ = _ := by ring
  change |(inner ℝ ((1-R) x) x)/‖x‖^2| ≤ 1
  simp only [sub_apply,one_apply_eq_self,inner_sub_left,real_inner_self_eq_norm_sq]
  rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hu) (sq_nonneg _))]
  by_cases hx : x=0
  · simp [hx]
  · apply (div_le_one (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr
    linarith

theorem positive_contraction_exists_sqrt (R : H →L[ℝ] H)
    (hR : R.IsPositive) (hn : ‖R‖ ≤ 1) :
    ∃ B : H →L[ℝ] H, B.IsPositive ∧ B*B=R := by
  obtain ⟨P,hP,hPn,hfix⟩ := sqrtComplementIter_exists_limit (1-R) (positive_contraction_complement_norm R hR hn)
  have hsX : IsSelfAdjoint (1-R) := (IsSelfAdjoint.one (H →L[ℝ] H)).sub hR.isSelfAdjoint
  have hsP : IsSelfAdjoint P := by
    apply (isClosed_eq continuous_star continuous_id).mem_of_tendsto hP
    exact Filter.Eventually.of_forall (sqrtComplementIter_selfAdjoint (1-R) hsX)
  refine ⟨1-P,?_,?_⟩
  · apply (ContinuousLinearMap.isPositive_iff' _).mpr
    refine ⟨(IsSelfAdjoint.one (H →L[ℝ] H)).sub hsP,?_⟩
    intro x
    simp only [sub_apply,one_apply_eq_self,inner_sub_left,real_inner_self_eq_norm_sq]
    have hp : inner ℝ (P x) x ≤ ‖x‖^2 := calc
      _ ≤ ‖P x‖*‖x‖ := (le_abs_self _).trans (abs_real_inner_le_norm _ _)
      _ ≤ ‖x‖*‖x‖ := mul_le_mul_of_nonneg_right
        ((P.le_opNorm x).trans (by nlinarith [norm_nonneg x])) (norm_nonneg x)
      _ = _ := by ring
    linarith
  · simpa only [sub_sub_cancel] using sqrtComplementIter_limit_square (1-R) P hfix

theorem positive_exists_sqrt (R : H →L[ℝ] H) (hR : R.IsPositive) :
    ∃ B : H →L[ℝ] H, B.IsPositive ∧ B*B=R := by
  let K := max 1 ‖R‖
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKi : 0 ≤ K⁻¹ := inv_nonneg.mpr hK.le
  have hnorm : ‖K⁻¹ • R‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hKi]
    exact (inv_mul_le_one₀ hK).mpr (le_max_right _ _)
  obtain ⟨B,hB,hBB⟩ := positive_contraction_exists_sqrt (K⁻¹ • R) (hR.smul_of_nonneg hKi) hnorm
  refine ⟨Real.sqrt K • B,hB.smul_of_nonneg (Real.sqrt_nonneg K),?_⟩
  rw [smul_mul_smul_comm,hBB,Real.mul_self_sqrt hK.le,smul_smul,mul_inv_cancel₀ (ne_of_gt hK),one_smul]

end Carleman
