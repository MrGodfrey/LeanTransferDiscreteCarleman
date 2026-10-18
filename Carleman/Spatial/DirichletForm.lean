module

public import Carleman.Spatial.DirichletPoincare
public import Carleman.Section3.OriginalForm

/-! The genuine Dirichlet gradient form on H¹₀. Boundedness and symmetry
come from the actual L² gradient; coercivity is proved by Poincare. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem WeakSobolevJet.norm_zero_field (u : WeakSobolevJet d 1 (volume.restrict S) S) :
    ‖WeakSobolevJet.field 0 u‖ = ‖WeakSobolevJet.value u‖ := by
  have he : ∀ᵐ x ∂volume.restrict S,
      ‖WeakSobolevJet.field 0 u x‖ = ‖WeakSobolevJet.value u x‖ := by
    filter_upwards [derivativeComponent_ae Sym.nil (WeakSobolevJet.field 0 u)] with x hx
    change WeakSobolevJet.value u x = WeakSobolevJet.field 0 u x Sym.nil at hx
    rw [hx,Real.norm_eq_abs]
    have hh := derivativeFiber_zero_norm_sq (WeakSobolevJet.field 0 u x)
    nlinarith [norm_nonneg (WeakSobolevJet.field 0 u x),abs_nonneg (WeakSobolevJet.field 0 u x Sym.nil),
      sq_abs (WeakSobolevJet.field 0 u x Sym.nil)]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ hx => hx.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ hx => hx.ge))

abbrev DirichletEnergy (S : Set (SpatialCoordinates d)) :=
  conformingHilbert (m := 1) (S := S) (dirichletSubspace S)

def dirichletGradient (S : Set (SpatialCoordinates d)) :
    DirichletEnergy S →L[ℝ] Lp (DerivativeFiber d 1) 2 (volume.restrict S) :=
  (WeakSobolevJet.fieldCLM 1).comp
    (SobolevHilbert.toJet.comp (conformingHilbert (m := 1) (S := S) (dirichletSubspace S)).subtypeL)

def dirichletForm (S : Set (SpatialCoordinates d)) :
    DirichletEnergy S →L[ℝ] DirichletEnergy S →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (dirichletGradient S) (dirichletGradient S)

theorem dirichletForm_apply (u v : DirichletEnergy S) :
    dirichletForm S u v = inner ℝ (dirichletGradient S u) (dirichletGradient S v) := rfl

theorem dirichletForm_symmetric (u v : DirichletEnergy S) :
    dirichletForm S u v = dirichletForm S v u := by
  simp only [dirichletForm_apply]
  exact real_inner_comm _ _

theorem dirichletForm_integral (u v : DirichletEnergy S) :
    dirichletForm S u v = ∫ x, ∑ α : Sym (Fin d) 1,
      dirichletGradient S u x α * dirichletGradient S v x α ∂volume.restrict S := by
  rw [dirichletForm_apply,L2.inner_def]
  congr 1
  funext x
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem dirichletEnergy_norm_sq (u : DirichletEnergy S) :
    ‖u‖^2 = ‖conformingEmbed (m := 1) (S := S) (dirichletSubspace S) u‖^2 +
      ‖dirichletGradient S u‖^2 := by
  have hh := SobolevHilbert.norm_sq u.val
  rw [Fin.sum_univ_two,WeakSobolevJet.norm_zero_field] at hh
  exact hh

theorem dirichletForm_coercive (hS : IsOpen S) (i : Fin d) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ S, |x i| ≤ R) (u : DirichletEnergy S) :
    ((2*R)^2+1)⁻¹ * ‖u‖ * ‖u‖ ≤ dirichletForm S u u := by
  have hu : SobolevHilbert.toJet u.val ∈ dirichletJetSpace S :=
    (mem_dirichletJetSpace_iff S hS _).mpr u.property
  have hp := dirichlet_poincare hS i hR0 hR _ hu
  change ‖conformingEmbed (m := 1) (S := S) (dirichletSubspace S) u‖ ≤
    2*R*‖dirichletGradient S u‖ at hp
  have hs := sq_le_sq₀ (norm_nonneg _) (show 0 ≤ 2*R*‖dirichletGradient S u‖ by positivity) |>.mpr hp
  have hk : 0 < (2*R)^2+1 := by positivity
  have hbound : ‖u‖^2 ≤ ((2*R)^2+1)*‖dirichletGradient S u‖^2 := by
    rw [dirichletEnergy_norm_sq]
    nlinarith only [hs]
  rw [dirichletForm_apply,real_inner_self_eq_norm_sq]
  have hdiv := (div_le_iff₀ hk).mpr (by nlinarith only [hbound] : ‖u‖^2 ≤ ‖dirichletGradient S u‖^2*((2*R)^2+1))
  convert hdiv using 1; ring

def dirichletOriginalForm (hS : IsOpen S) (i : Fin d) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ S, |x i| ≤ R) :
    OriginalForm (m := 1) (ν := volume.restrict S) hS (ae_restrict_mem hS.measurableSet) where
  V := dirichletSubspace S
  sobolev := dirichletSubspace_sobolev S
  closed := dirichletSubspace_closed S hS
  dense := dirichletSubspace_dense S hS
  form := dirichletForm S
  symmetric := dirichletForm_symmetric
  coercive := ⟨((2*R)^2+1)⁻¹,by positivity,dirichletForm_coercive hS i hR0 hR⟩

theorem dirichletForm_coercive_of_bounded (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) :
    ∃ c > (0 : ℝ), ∀ u : DirichletEnergy S, c*‖u‖*‖u‖ ≤ dirichletForm S u u := by
  obtain ⟨R,hR0,hR⟩ := hb.exists_pos_norm_le
  refine ⟨((2*R)^2+1)⁻¹,by positivity,?_⟩
  apply dirichletForm_coercive hS (⟨0,hd⟩ : Fin d) hR0.le
  intro x hx
  have hn : |x (⟨0,hd⟩ : Fin d)| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (⟨0,hd⟩ : Fin d)
  exact hn.trans (hR x hx)

def boundedDirichletOriginalForm (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) :
    OriginalForm (m := 1) (ν := volume.restrict S) hS (ae_restrict_mem hS.measurableSet) where
  V := dirichletSubspace S
  sobolev := dirichletSubspace_sobolev S
  closed := dirichletSubspace_closed S hS
  dense := dirichletSubspace_dense S hS
  form := dirichletForm S
  symmetric := dirichletForm_symmetric
  coercive := dirichletForm_coercive_of_bounded hS hd hb

end Carleman
