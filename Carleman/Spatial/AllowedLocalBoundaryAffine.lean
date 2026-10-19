module

public import Carleman.Spatial.WeightedLocalBoundaryAffine
public import Carleman.Spatial.BoxAllowedComparison

/-! The paper's actual allowed weight family supplies every local comparison
internally. Every original H²∩H¹₀ state has the uniform weighted local affine
approximation, for both weight signs and arbitrary powers, whenever hq≤1. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates (d+1))}

theorem allowed_weight_dirichlet_h2_local_boundary_affine
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (a b : Fin (d+1) → ℝ) (_hpos : ∀ i, a i < b i)
      (hBS : openCoordinateBox a b ⊆ S) (h : ℝ),
      0 < h → (∀ i, h/κ ≤ b i-a i) → (∀ i, b i-a i ≤ κ*h) →
      ∀ J : Finset (Fin (d+1) × Bool),
      (∀ f ∈ J, coordinateClosedFace f.1 a b f.2 ⊆ frontier S) →
      ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → h*w.q t ≤ 1 →
      ∀ u : WeakSobolevJet (d+1) 2 (volume.restrict S) S,
      WeakSobolevJet.value u ∈ dirichletSubspace S →
      ∃ (p : SpatialCoordinates (d+1) →ᵃ[ℝ] ℝ)
        (r : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a b f.2, p y=0) ∧
        (WeakSobolevJet.value r =ᵐ[volume.restrict (openCoordinateBox a b)]
          (fun x => WeakSobolevJet.value u x-p x)) ∧
        (((ρ.scaled η).multiplier w τ t).onSubdomain hBS).seminorm (WeakSobolevJet.value r)+
          h*(((ρ.scaled η).multiplier w τ t).onSubdomain hBS).seminorm (WeakSobolevJet.field 1 r) ≤
          C*h^2*‖subdomainLp hBS (((ρ.scaled η).multiplier w τ t).map (WeakSobolevJet.field 2 u))‖ := by
  obtain ⟨L,hL,hLip⟩ := smooth_profile_lipschitz hS hc hcompact hρ
  obtain ⟨C,hC,hbound⟩ := weighted_dirichlet_h2_local_boundary_affine d κ
    (Real.exp (L*(d+1:ℕ)*κ)) hκ (Real.exp_pos _)
  refine ⟨C,hC,?_⟩
  intro a b hpos hBS h hh hlower hupper J hfaces w τ t η hη hm u hu
  obtain ⟨y,hy⟩ := openCoordinateBox_nonempty a b hpos
  apply hbound S hS a b hpos hBS h hh hlower hupper J hfaces
    ((ρ.scaled η).multiplier w τ t) (((ρ.scaled η).multiplier w τ t).value y)
    (ρ.scaled_multiplier_pos η w τ t y) ?_ u hu
  filter_upwards [ae_restrict_mem (openCoordinateBox_isOpen a b).measurableSet] with x hx
  exact allowedWeight_box_comparison ρ L κ (by linarith) (by linarith) hLip a b hpos hBS h hh
    hupper w τ t η hη hm hx hy

end Carleman
