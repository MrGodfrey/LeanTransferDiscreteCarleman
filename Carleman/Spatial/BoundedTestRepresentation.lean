module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! A bounded functional on an actual test subspace has a Hilbert-space
representative with the same bound. No completeness of the test space or
pre-existing weak derivative is assumed. -/
@[expose] public noncomputable section
namespace Carleman

theorem exists_inner_of_bounded_test_functional
    {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (J : V →ₗ[ℝ] H) (hJ : Function.Injective J) (L : V →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |L x| ≤ C*‖J x‖) :
    ∃ v : H, ‖v‖ ≤ C ∧ ∀ x, inner ℝ v (J x) = L x := by
  let e := LinearEquiv.ofInjective J hJ
  let l : LinearMap.range J →ₗ[ℝ] ℝ := L.comp e.symm.toLinearMap
  have hb (x : LinearMap.range J) : ‖l x‖ ≤ C*‖x‖ := by
    have hx : J (e.symm x) = (x : H) := LinearEquiv.ofInjective_symm_apply J x
    simpa only [l,LinearMap.comp_apply,LinearEquiv.coe_coe,Real.norm_eq_abs,hx,
      Submodule.norm_coe] using hbound (e.symm x)
  let f := l.mkContinuous C hb
  obtain ⟨g,hg,hgn⟩ := exists_extension_norm_eq (LinearMap.range J) f
  refine ⟨(InnerProductSpace.toDual ℝ H).symm g,?_,?_⟩
  · rw [(InnerProductSpace.toDual ℝ H).symm.norm_map,hgn]
    exact LinearMap.mkContinuous_norm_le _ hC hb
  · intro x
    rw [InnerProductSpace.toDual_symm_apply]
    have hx := hg (e x)
    change g (J x) = f (e x) at hx
    simpa only [f,LinearMap.mkContinuous_apply,l,LinearMap.comp_apply,
      LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hx

end Carleman
