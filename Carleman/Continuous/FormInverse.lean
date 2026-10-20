module

public import Carleman.Continuous.FormSelfAdjoint
public import Mathlib.Analysis.InnerProductSpace.Positive

/-! The actual inverse of the original coercive form operator and its energy identities. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

def inverseH : H →L[ℝ] H := b.embed.comp (b.resolventEnergy 0 le_rfl)

omit [CompleteSpace H] in
theorem inverseH_eq (f : H) : b.inverseH f=(b.resolvent 0 le_rfl f : H) := rfl

omit [CompleteSpace H] in
theorem inverseH_form (f : H) (v : V) :
    b.form (b.resolventEnergy 0 le_rfl f) v=inner ℝ f (b.embed v) := by
  simpa only [zero_smul,sub_zero] using b.resolventEnergy_test 0 le_rfl f v

omit [CompleteSpace H] in
theorem inverseH_pair (f g : H) :
    inner ℝ (b.inverseH f) g=inner ℝ f (b.inverseH g) := by
  rw [real_inner_comm]
  change inner ℝ g (b.embed (b.resolventEnergy 0 le_rfl f))=inner ℝ f (b.embed (b.resolventEnergy 0 le_rfl g))
  rw [←b.inverseH_form,←b.inverseH_form,b.symmetric]

omit [CompleteSpace H] in
omit [CompleteSpace H] in
theorem inverseH_positive : b.inverseH.IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨b.inverseH_pair,?_⟩
  intro f
  rw [real_inner_comm]
  exact (b.form_nonneg (b.resolventEnergy 0 le_rfl f)).trans_eq (b.inverseH_form f _)

omit [CompleteSpace H] in
omit [CompleteSpace H] in
theorem inverseH_injective : Function.Injective b.inverseH := by
  intro f g h
  have hz : b.resolvent 0 le_rfl f=b.resolvent 0 le_rfl g := Subtype.ext h
  have hf := b.resolvent_equation 0 le_rfl f
  have hg := b.resolvent_equation 0 le_rfl g
  simp only [zero_smul,add_zero] at hf hg
  exact hf.symm.trans ((congrArg b.operator hz).trans hg)

omit [CompleteSpace H] in
omit [CompleteSpace H] in
theorem inverseH_range : b.inverseH.toLinearMap.range=b.domain := by
  ext x
  constructor
  · rintro ⟨f,rfl⟩
    exact (b.resolvent 0 le_rfl f).property
  · intro hx
    let z : b.domain := ⟨x,hx⟩
    refine ⟨b.operator z,?_⟩
    have he : z=b.resolvent 0 le_rfl (b.operator z) :=
      b.resolvent_unique 0 le_rfl _ (by simp only [zero_smul,add_zero])
    exact (congrArg Subtype.val he).symm

theorem inverseH_dense : DenseRange b.inverseH := by
  change Dense (b.inverseH.toLinearMap.range : Set H)
  rw [b.inverseH_range]
  exact b.domain_dense

omit [CompleteSpace H] in
theorem inverseEnergy_dense : DenseRange (b.resolventEnergy 0 le_rfl) := by
  change Dense ((b.resolventEnergy 0 le_rfl).toLinearMap.range : Set V)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm ?_ bot_le
  intro y hy
  change y=0
  let w := b.coercive.continuousLinearEquivOfBilin.symm y
  have hw : b.coercive.continuousLinearEquivOfBilin w=y :=
    b.coercive.continuousLinearEquivOfBilin.apply_symm_apply y
  have ht (f : H) : inner ℝ f (b.embed w)=0 := by
    rw [←b.inverseH_form,b.symmetric,←b.coercive.continuousLinearEquivOfBilin_apply,hw,real_inner_comm]
    exact ((b.resolventEnergy 0 le_rfl).toLinearMap.range.mem_orthogonal y).mp hy _ ⟨f,rfl⟩
  have he : b.embed w=0 := by
    have hn := ht (b.embed w)
    rw [real_inner_self_eq_norm_sq] at hn
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (b.embed w)])
  have hw0 : w=0 := b.injective (by simpa only [map_zero] using he)
  rw [hw0,map_zero] at hw
  exact hw.symm

omit [CompleteSpace H] in
theorem inverseSqrt_injective (B : H →L[ℝ] H) (hBB : B*B=b.inverseH) : Function.Injective B := by
  intro f g h
  apply b.inverseH_injective
  rw [←hBB]
  exact congrArg B h

theorem inverseSqrt_dense (B : H →L[ℝ] H) (hBB : B*B=b.inverseH) : DenseRange B := by
  apply b.inverseH_dense.mono
  rintro _ ⟨f,rfl⟩
  refine ⟨B f,?_⟩
  exact congrArg (fun T : H →L[ℝ] H => T f) hBB

omit [CompleteSpace H] in
theorem inverseSqrt_energy_pair (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH)
    (f g : H) :
    b.form (b.resolventEnergy 0 le_rfl f) (b.resolventEnergy 0 le_rfl g)=inner ℝ (B f) (B g) := by
  rw [b.inverseH_form,hB.inner_left_eq_inner_right]
  exact congrArg (fun z => inner ℝ f z) (congrArg (fun T : H →L[ℝ] H => T g) hBB.symm)

omit [CompleteSpace H] in
theorem inverseSqrt_energy_bound (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) :
    ∃ C > (0:ℝ), ∀ f : H, ‖b.resolventEnergy 0 le_rfl f‖ ≤ C*‖B f‖ := by
  obtain ⟨c,hc,hcoer⟩ := b.coercive
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨(Real.sqrt c)⁻¹,inv_pos.mpr hs,?_⟩
  intro f
  have hh := hcoer (b.resolventEnergy 0 le_rfl f)
  rw [b.inverseSqrt_energy_pair B hB hBB,real_inner_self_eq_norm_sq] at hh
  have he := Real.sq_sqrt hc.le
  have hb : Real.sqrt c*‖b.resolventEnergy 0 le_rfl f‖ ≤ ‖B f‖ := by
    apply (sq_le_sq₀ (mul_nonneg hs.le (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow,he]
    nlinarith only [hh]
  calc
    _ = (Real.sqrt c)⁻¹*(Real.sqrt c*‖b.resolventEnergy 0 le_rfl f‖) := by
      rw [←mul_assoc,inv_mul_cancel₀ (ne_of_gt hs),one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hs.le)

end Carleman.CoerciveForm
