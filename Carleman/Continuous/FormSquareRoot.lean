module

public import Carleman.Continuous.FormSquareRootLift
public import Carleman.Continuous.RealOperatorSquareRoot

/-! The positive self-adjoint square root has exactly the original form domain; its full square graph is the original operator. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

def formSqrtDomain : Submodule ℝ H := b.embed.toLinearMap.range

def formSqrt (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) :
    b.formSqrtDomain →ₗ[ℝ] H :=
  (LinearEquiv.ofInjective B.toLinearMap (b.inverseSqrt_injective B hBB)).symm.toLinearMap.comp
    (b.formSqrtDomain.inclusion (b.inverseSqrt_range B hB hBB).ge)

theorem formSqrt_inverse (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH)
    (v : b.formSqrtDomain) : B (b.formSqrt B hB hBB v)=(v : H) := by
  let e := LinearEquiv.ofInjective B.toLinearMap (b.inverseSqrt_injective B hBB)
  exact congrArg Subtype.val (e.apply_symm_apply
    (b.formSqrtDomain.inclusion (b.inverseSqrt_range B hB hBB).ge v))

theorem formSqrt_graph (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) (x f : H) :
    (∃ v : b.formSqrtDomain, (v : H)=x ∧ b.formSqrt B hB hBB v=f) ↔ B f=x := by
  constructor
  · rintro ⟨v,rfl,rfl⟩
    exact b.formSqrt_inverse B hB hBB v
  · intro h
    have hx : x ∈ b.formSqrtDomain := (b.inverseSqrt_range B hB hBB).le ⟨f,h⟩
    refine ⟨⟨x,hx⟩,rfl,?_⟩
    apply b.inverseSqrt_injective B hBB
    exact (b.formSqrt_inverse B hB hBB ⟨x,hx⟩).trans h.symm

theorem formSqrt_energy (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) (v : V) :
    ‖b.formSqrt B hB hBB ⟨b.embed v,⟨v,rfl⟩⟩‖^2=b.form v v := by
  let x := b.formSqrt B hB hBB ⟨b.embed v,⟨v,rfl⟩⟩
  have hv : b.inverseSqrtLift B x=v := by
    apply b.injective
    rw [b.inverseSqrtLift_embed B hB hBB]
    exact b.formSqrt_inverse B hB hBB _
  have hp := b.inverseSqrtLift_pair B hB hBB x x
  rw [hv,real_inner_self_eq_norm_sq] at hp
  exact hp.symm

theorem formSqrt_nonneg (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH)
    (v : b.formSqrtDomain) : 0 ≤ inner ℝ (b.formSqrt B hB hBB v) (v : H) := by
  rw [←b.formSqrt_inverse B hB hBB v]
  exact hB.inner_nonneg_right _

theorem formSqrt_adjoint_graph (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) (y g : H) :
    (∀ v : b.formSqrtDomain, inner ℝ (b.formSqrt B hB hBB v) y=inner ℝ (v : H) g) ↔
      ∃ v : b.formSqrtDomain, (v : H)=y ∧ b.formSqrt B hB hBB v=g := by
  rw [b.formSqrt_graph B hB hBB]
  constructor
  · intro h
    apply ext_inner_left ℝ
    intro f
    obtain ⟨v,hv,hs⟩ := (b.formSqrt_graph B hB hBB (B f) f).mpr rfl
    have hh := h v
    rw [hv,hs,hB.inner_left_eq_inner_right] at hh
    exact hh.symm
  · intro h v
    rw [←h,←hB.inner_left_eq_inner_right,b.formSqrt_inverse B hB hBB v]

omit [CompleteSpace H] in
theorem inverseH_operator_graph (x f : H) :
    (∃ z : b.domain, (z : H)=x ∧ b.operator z=f) ↔ b.inverseH f=x := by
  constructor
  · rintro ⟨z,rfl,rfl⟩
    exact (congrArg Subtype.val (b.resolvent_unique 0 le_rfl (b.operator z)
      (v := z) (by simp only [zero_smul,add_zero]))).symm
  · intro h
    refine ⟨b.resolvent 0 le_rfl f,h,?_⟩
    simpa only [zero_smul,add_zero] using b.resolvent_equation 0 le_rfl f

theorem formSqrt_square_graph (B : H →L[ℝ] H) (hB : B.IsPositive) (hBB : B*B=b.inverseH) (x f : H) :
    (∃ v : b.formSqrtDomain, (v : H)=x ∧ ∃ u : b.formSqrtDomain,
      (u : H)=b.formSqrt B hB hBB v ∧ b.formSqrt B hB hBB u=f) ↔
    ∃ z : b.domain, (z : H)=x ∧ b.operator z=f := by
  rw [b.inverseH_operator_graph]
  constructor
  · rintro ⟨v,hv,u,hu,hf⟩
    have h1 := b.formSqrt_inverse B hB hBB v
    have h2 := b.formSqrt_inverse B hB hBB u
    rw [hf,hu] at h2
    rw [←hBB]
    change B (B f)=x
    rw [h2,h1,hv]
  · intro h
    have he : B (B f)=x := (congrArg (fun T : H →L[ℝ] H => T f) hBB).trans h
    obtain ⟨v,hv,hSv⟩ := (b.formSqrt_graph B hB hBB x (B f)).mpr he
    obtain ⟨u,hu,hSu⟩ := (b.formSqrt_graph B hB hBB (B f) f).mpr rfl
    exact ⟨v,hv,u,hu.trans hSv.symm,hSu⟩

theorem exists_positive_form_square_root :
    ∃ Ahalf : b.formSqrtDomain →ₗ[ℝ] H,
      (∀ v : b.formSqrtDomain, 0 ≤ inner ℝ (Ahalf v) (v : H)) ∧
      (∀ y g : H, (∀ v : b.formSqrtDomain, inner ℝ (Ahalf v) y=inner ℝ (v : H) g) ↔
        ∃ v : b.formSqrtDomain, (v : H)=y ∧ Ahalf v=g) ∧
      (∀ x f : H, (∃ v : b.formSqrtDomain, (v : H)=x ∧
        ∃ u : b.formSqrtDomain, (u : H)=Ahalf v ∧ Ahalf u=f) ↔
        ∃ z : b.domain, (z : H)=x ∧ b.operator z=f) ∧
      ∀ v : V, ‖Ahalf ⟨b.embed v,⟨v,rfl⟩⟩‖^2=b.form v v := by
  obtain ⟨B,hB,hBB⟩ := Carleman.positive_exists_sqrt b.inverseH b.inverseH_positive
  exact ⟨b.formSqrt B hB hBB,b.formSqrt_nonneg B hB hBB,b.formSqrt_adjoint_graph B hB hBB,
    b.formSqrt_square_graph B hB hBB,b.formSqrt_energy B hB hBB⟩

end Carleman.CoerciveForm
