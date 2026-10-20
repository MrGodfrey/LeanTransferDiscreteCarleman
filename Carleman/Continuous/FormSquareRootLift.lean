module

public import Carleman.Continuous.FormInverse
public import Mathlib.Analysis.Normed.Operator.Extend

/-! The inverse square root lifts onto exactly the full original form energy space. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

def inverseSqrtLift (B : H →L[ℝ] H) : H →L[ℝ] V :=
  (b.resolventEnergy 0 le_rfl).toLinearMap.extendOfNorm B.toLinearMap

theorem inverseSqrtLift_apply (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) (f : H) :
    b.inverseSqrtLift B (B f)=b.resolventEnergy 0 le_rfl f := by
  obtain ⟨C,_,hC⟩ := b.inverseSqrt_energy_bound B hB hBB
  exact LinearMap.extendOfNorm_eq (b.inverseSqrt_dense B hBB) ⟨C,hC⟩ f

theorem inverseSqrtLift_pair (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) (x y : H) :
    b.form (b.inverseSqrtLift B x) (b.inverseSqrtLift B y)=inner ℝ x y := by
  have hd := (b.inverseSqrt_dense B hBB).prodMap (b.inverseSqrt_dense B hBB)
  have he : (fun p : H×H => b.form (b.inverseSqrtLift B p.1) (b.inverseSqrtLift B p.2))=
      (fun p : H×H => inner ℝ p.1 p.2) := by
    apply hd.equalizer (by fun_prop) (by fun_prop)
    funext p
    change b.form (b.inverseSqrtLift B (B p.1)) (b.inverseSqrtLift B (B p.2))=inner ℝ (B p.1) (B p.2)
    rw [b.inverseSqrtLift_apply B hB hBB,b.inverseSqrtLift_apply B hB hBB]
    exact b.inverseSqrt_energy_pair B hB hBB p.1 p.2
  exact congrFun he (x,y)

theorem inverseSqrtLift_embed (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) (x : H) :
    b.embed (b.inverseSqrtLift B x)=B x := by
  have he : (fun y : H => b.embed (b.inverseSqrtLift B y))=B := by
    apply (b.inverseSqrt_dense B hBB).equalizer (by fun_prop) B.continuous
    funext f
    change b.embed (b.inverseSqrtLift B (B f))=B (B f)
    rw [b.inverseSqrtLift_apply B hB hBB]
    exact congrArg (fun T : H →L[ℝ] H => T f) hBB.symm
  exact congrFun he x

theorem inverseSqrtLift_lower_bound (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) (x : H) :
    ‖x‖ ≤ (1+‖b.form‖)*‖b.inverseSqrtLift B x‖ := by
  let v := b.inverseSqrtLift B x
  have he : b.form v v=‖x‖^2 := by rw [b.inverseSqrtLift_pair B hB hBB,real_inner_self_eq_norm_sq]
  have hb : ‖x‖^2 ≤ ‖b.form‖*‖v‖^2 := by
    calc
      _ = |b.form v v| := by rw [he,abs_of_nonneg (sq_nonneg _)]
      _ ≤ ‖b.form v‖*‖v‖ := (b.form v).le_opNorm v
      _ ≤ (‖b.form‖*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right (b.form.le_opNorm v) (norm_nonneg _)
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  rw [mul_pow]
  exact hb.trans (mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg b.form]) (sq_nonneg _))

theorem inverseSqrtLift_surjective (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) :
    Function.Surjective (b.inverseSqrtLift B) := by
  have hd : DenseRange (b.inverseSqrtLift B) := by
    apply b.inverseEnergy_dense.mono
    rintro _ ⟨f,rfl⟩
    exact ⟨B f,b.inverseSqrtLift_apply B hB hBB f⟩
  have ha := (b.inverseSqrtLift B).antilipschitz_of_bound (K := ⟨1+‖b.form‖,by positivity⟩)
    (b.inverseSqrtLift_lower_bound B hB hBB)
  have hc := ha.isClosed_range (b.inverseSqrtLift B).uniformContinuous
  intro v
  have hv := hd v
  rwa [hc.closure_eq] at hv

theorem inverseSqrt_range (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) :
    B.toLinearMap.range=b.embed.toLinearMap.range := by
  ext v
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨b.inverseSqrtLift B x,b.inverseSqrtLift_embed B hB hBB x⟩
  · rintro ⟨u,rfl⟩
    obtain ⟨x,hx⟩ := b.inverseSqrtLift_surjective B hB hBB u
    exact ⟨x,(b.inverseSqrtLift_embed B hB hBB x).symm.trans (congrArg b.embed hx)⟩


end Carleman.CoerciveForm
