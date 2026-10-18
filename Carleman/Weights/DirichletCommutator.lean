module

public import Carleman.Spatial.LaplacianCorrectionBounds
public import Carleman.Spatial.DirichletCommutatorIdentity

/-! The original m=1 commutator estimate for the genuine Dirichlet form
operator. One constant precedes every allowed weight and every domain state. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem allowed_laplacian_correction_conjugated (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1)
      (u v : WeakSobolevJet d 1 (volume.restrict S) S),
      WeakSobolevJet.value v=((ρ.scaled η).multiplier w τ t).map (WeakSobolevJet.value u) →
      ‖smoothLaplacianCorrection hS ((ρ.scaled η).multiplier w τ t)
        (allowed_multiplier_boundedSmooth hS hb ρ hρ w τ t η hη) u‖ ≤
        C*(w.q t^2*‖WeakSobolevJet.value v‖+w.q t*‖WeakSobolevJet.field 1 v‖) := by
  obtain ⟨B,hB,hcorr⟩ := allowed_laplacian_correction_uniform hS hb ρ hρ
  obtain ⟨D,hD,hconj⟩ := intrinsic_allowedWeight_parameterNorm_uniform (n := 1) (ν := volume.restrict S)
    hS (ae_restrict_mem hS.measurableSet) (hρ.boundedSmoothOn hb)
  refine ⟨B*D,mul_pos hB hD,?_⟩
  intro w τ t η hη u v hv
  have he : ((ρ.scaled η).multiplier w τ t).value =
      (fun x => w.q t^τ*Real.exp (w.q t*(η*ρ.value x))) := by
    funext x
    change w.q t^τ*Real.exp ((η*ρ.value x)*w.q t) = _
    rw [mul_comm (η*ρ.value x)]
  have hh := (hconj (w.q t) (w.lower t) τ η hη _ he u v hv).2
  have hc := hcorr w τ t η hη u
  have hs := mul_le_mul_of_nonneg_left hh (mul_nonneg hB.le (w.nonneg t))
  rw [WeakSobolevJet.heat_parameterNorm (w.q t) BoundedMultiplier.one v,BoundedMultiplier.one_seminorm,
    BoundedMultiplier.one_seminorm] at hs
  exact hc.trans (by convert hs using 1; ring)

set_option maxHeartbeats 1200000 in
theorem dirichlet_allowed_commutator_uniform (hS : IsOpen S) (hd : 0 < d)
    (hb : Bornology.IsBounded S) (ρ : SpatialProfile (volume.restrict S))
    (hρ : SmoothOnClosure ρ.value S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1),
    let σ := (ρ.scaled η).multiplier w τ t
    let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
    let hσ := allowed_weight_mem_dirichlet_domain hS hd hb ρ hρ w τ t η hη
    let hξ := allowed_weight_mem_dirichlet_domain hS hd hb ρ hρ w (-τ) t (-η) (by simpa using hη)
    ∀ z : (boundedDirichletOriginalForm hS hd hb).model.domain,
      ‖conjugatedCommutator (boundedDirichletOriginalForm hS hd hb).model.operator σ ξ hσ hξ z‖ ≤
        C*(w.q t^2*‖(z : Lp ℝ 2 (volume.restrict S))‖+
          w.q t*‖WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb z)‖) := by
  obtain ⟨C,hC,hbound⟩ := allowed_laplacian_correction_conjugated hS hb ρ hρ
  refine ⟨C,hC,?_⟩
  intro w τ t η hη
  dsimp only
  intro z
  let σ := (ρ.scaled η).multiplier w τ t
  let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
  let hp := allowed_weight_mem_dirichlet_domain hS hd hb ρ hρ w τ t η hη
  let hi := allowed_weight_mem_dirichlet_domain hS hd hb ρ hρ w (-τ) t (-η) (by simpa using hη)
  have hinv : ∀ᵐ x ∂volume.restrict S, σ.value x*ξ.value x=1 := by
    apply Filter.Eventually.of_forall
    intro x
    change (w.q t^τ*Real.exp ((η*ρ.value x)*w.q t))*
      (w.q t^(-τ)*Real.exp (((-η)*ρ.value x)*w.q t))=1
    have he : (-η)*ρ.value x*w.q t=-(η*ρ.value x*w.q t) := by ring
    rw [he,Real.exp_neg,Real.rpow_neg (w.nonneg t)]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (w.pos t) τ)]
  let u := dirichletDomainJet hS hd hb (conformingWeight ξ hi z)
  let v := dirichletDomainJet hS hd hb z
  have hv : WeakSobolevJet.value v=σ.map (WeakSobolevJet.value u) := by
    dsimp only [u,v]
    rw [dirichletDomainJet_value,dirichletDomainJet_value]
    exact (σ.map_inverse ξ hinv (z : Lp ℝ 2 (volume.restrict S))).symm
  have he := dirichlet_conjugatedCommutator_eq hS hd hb σ ξ
    (allowed_multiplier_boundedSmooth hS hb ρ hρ w τ t η hη) hp hi z
  rw [he,norm_neg]
  have hh := hbound w τ t η hη u v hv
  rw [dirichletDomainJet_value] at hh
  exact hh

end Carleman
