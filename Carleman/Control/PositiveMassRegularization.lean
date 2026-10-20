module

public import Carleman.Continuous.FormSolve

/-! Actual positive mass-shift inverses and contraction estimates from Lax–Milgram. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter InnerProductSpace
open scoped Topology
namespace Carleman
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def positiveMassForm (M : V →L[ℝ] V) (ε : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ).comp M+ε • innerSL ℝ

omit [CompleteSpace V] in
theorem positiveMassForm_coercive (M : V →L[ℝ] V)
    (hM : ∀ v, 0 ≤ inner ℝ (M v) v) {ε : ℝ} (hε : 0 < ε) :
    IsCoercive (positiveMassForm M ε) := by
  refine ⟨ε,hε,fun v => ?_⟩
  change ε*‖v‖*‖v‖ ≤ inner ℝ (M v) v+ε*inner ℝ v v
  rw [real_inner_self_eq_norm_sq]
  nlinarith [hM v]

def positiveMassInverse (M : V →L[ℝ] V) (hM : ∀ v, 0 ≤ inner ℝ (M v) v)
    (ε : ℝ) (hε : 0 < ε) : V →L[ℝ] V :=
  (variationalSolve (positiveMassForm M ε) (positiveMassForm_coercive M hM hε)).comp (innerSL ℝ)

theorem positiveMassInverse_equation (M : V →L[ℝ] V) (hM : ∀ v, 0 ≤ inner ℝ (M v) v)
    (ε : ℝ) (hε : 0 < ε) (x : V) :
    M (positiveMassInverse M hM ε hε x)+ε • positiveMassInverse M hM ε hε x=x := by
  apply ext_inner_right ℝ
  intro w
  have he := variationalSolve_spec (positiveMassForm M ε) (positiveMassForm_coercive M hM hε) (innerSL ℝ x) w
  change inner ℝ (M (positiveMassInverse M hM ε hε x)) w+ε*inner ℝ (positiveMassInverse M hM ε hε x) w=inner ℝ x w at he
  simpa only [inner_add_left,real_inner_smul_left] using he

theorem positiveMassInverse_left (M : V →L[ℝ] V) (hM : ∀ v, 0 ≤ inner ℝ (M v) v)
    (ε : ℝ) (hε : 0 < ε) (x : V) :
    positiveMassInverse M hM ε hε (M x+ε • x)=x := by
  symm
  apply variationalSolve_unique (positiveMassForm M ε) (positiveMassForm_coercive M hM hε) (innerSL ℝ (M x+ε • x))
  intro w
  change inner ℝ (M x) w+ε*inner ℝ x w=inner ℝ (M x+ε • x) w
  rw [inner_add_left,real_inner_smul_left]

theorem positiveMassInverse_commute (M : V →L[ℝ] V) (hM : ∀ v, 0 ≤ inner ℝ (M v) v)
    (ε : ℝ) (hε : 0 < ε) (x : V) :
    positiveMassInverse M hM ε hε (M x)=M (positiveMassInverse M hM ε hε x) := by
  have h₁ := positiveMassInverse_equation M hM ε hε x
  have h₂ := positiveMassInverse_left M hM ε hε x
  rw [map_add,map_smul] at h₂
  exact add_right_cancel (h₂.trans h₁.symm)

def positiveMassRegularizer (M : V →L[ℝ] V) (hM : ∀ v, 0 ≤ inner ℝ (M v) v)
    (ε : ℝ) (hε : 0 < ε) : V →L[ℝ] V := M.comp (positiveMassInverse M hM ε hε)

theorem positiveMassRegularizer_norm (M : V →L[ℝ] V) (hM : ∀ v, 0 ≤ inner ℝ (M v) v)
    (ε : ℝ) (hε : 0 < ε) (x : V) : ‖positiveMassRegularizer M hM ε hε x‖ ≤ ‖x‖ := by
  let z := positiveMassInverse M hM ε hε x
  have he : M z+ε • z=x := positiveMassInverse_equation M hM ε hε x
  have hip := congrArg (fun v => inner ℝ v (M z)) he
  simp only [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq] at hip
  have hp : 0 ≤ inner ℝ z (M z) := by rw [real_inner_comm]; exact hM z
  have hn : ‖M z‖^2 ≤ ‖x‖*‖M z‖ := by
    have hh := real_inner_le_norm x (M z)
    nlinarith [mul_nonneg hε.le hp]
  change ‖M z‖ ≤ ‖x‖
  nlinarith [norm_nonneg (M z),norm_nonneg x]

theorem positiveMassRegularizer_residual_norm (M : V →L[ℝ] V) (hM : ∀ v, 0 ≤ inner ℝ (M v) v)
    (ε : ℝ) (hε : 0 < ε) (x : V) : ‖x-positiveMassRegularizer M hM ε hε x‖ ≤ ‖x‖ := by
  let z := positiveMassInverse M hM ε hε x
  have he : M z+ε • z=x := positiveMassInverse_equation M hM ε hε x
  have hr : x-positiveMassRegularizer M hM ε hε x=ε • z := by
    change x-M z=ε • z
    rw [← he]; abel
  rw [hr,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
  have hip := congrArg (fun v => inner ℝ v z) he
  simp only [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq] at hip
  have hn : ε*‖z‖^2 ≤ ‖x‖*‖z‖ := by
    have hh := real_inner_le_norm x z
    linarith [hM z]
  by_cases hz : z=0
  · simp [hz]
  · have hzpos := norm_pos_iff.mpr hz
    nlinarith

theorem positiveMassRegularizer_range_error (M : V →L[ℝ] V) (hM : ∀ v, 0 ≤ inner ℝ (M v) v)
    (ε : ℝ) (hε : 0 < ε) (x : V) :
    ‖M x-positiveMassRegularizer M hM ε hε (M x)‖ ≤ ε*‖x‖ := by
  have he := congrArg M (positiveMassInverse_equation M hM ε hε x)
  rw [map_add,map_smul] at he
  have hr : M x-positiveMassRegularizer M hM ε hε (M x)=ε • positiveMassRegularizer M hM ε hε x := by
    change M x-M (positiveMassInverse M hM ε hε (M x))=ε • M (positiveMassInverse M hM ε hε x)
    rw [positiveMassInverse_commute]
    rw [← he]
    abel
  rw [hr,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
  exact mul_le_mul_of_nonneg_left (positiveMassRegularizer_norm M hM ε hε x) hε.le


end Carleman
