module

public import Carleman.Spatial.CartesianKuhnErrorAssembly
public import Carleman.Spatial.BoxAllowedComparison

/-! Appendix B.2: the actual moment reconstruction has the full allowed-weight
h² value/gradient estimate for every original H²∩H¹₀ state. Constants precede
all grids, time weights, powers, signs, times and states. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates (d+1))}

theorem allowed_weight_cartesianKuhn_h2_error
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
      (hTS : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ S) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → h*w.q t ≤ 1 →
      ∀ u : WeakSobolevJet (d+1) 2
        (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
        (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      WeakSobolevJet.value u ∈ dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) →
      let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
      let e := cartesianKuhnErrorJet o δ hδ N (WeakSobolevJet.truncate (by omega : 1 ≤ 2) u)
      σ.seminorm (WeakSobolevJet.value e)+h*σ.seminorm (WeakSobolevJet.field 1 e) ≤
        C*h^2*σ.seminorm (WeakSobolevJet.field 2 u) := by
  obtain ⟨L,hL,hLip⟩ := smooth_profile_lipschitz hS hc hcompact hρ
  let W := Real.exp (L*(d+1:ℕ)*5)
  have hW : 0 < W := Real.exp_pos _
  obtain ⟨A,hA,hlocal⟩ := cartesianKuhn_h2_weighted_local_error d κ W hκ hW
  let M : ℕ := 5^(d+1)*(d+1).factorial
  refine ⟨Real.sqrt (2*(M:ℝ))*A,by dsimp only [M]; positivity,?_⟩
  intro o δ hδ N hTS h hh hlower hupper w τ t η hη hm u hu
  dsimp only
  let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
  apply cartesianKuhn_error_assembly o δ hδ N A h hA.le hh.le σ _ (WeakSobolevJet.field 2 u)
  intro i
  let a := cartesianClippedPatchLower o δ N i
  let b := cartesianClippedPatchUpper o δ N i
  have hpos (j : Fin (d+1)) : a j < b j := by
    have hb := (cartesianClippedPatch_width_bounds o δ hδ N i j).1
    change δ j ≤ b j-a j at hb
    linarith [hδ j]
  have hBS : openCoordinateBox a b ⊆ S := by
    rw [← cartesianClippedPatch_eq_box]
    exact (cartesianClippedPatch_subset_domain o δ N i).trans hTS
  have hwidth (j : Fin (d+1)) : b j-a j ≤ 5*h :=
    (cartesianClippedPatch_width_bounds o δ hδ N i j).2.trans (mul_le_mul_of_nonneg_left (hupper j) (by norm_num))
  obtain ⟨y,hy⟩ := openCoordinateBox_nonempty a b hpos
  apply hlocal o δ hδ N i h hh hlower hupper σ (σ.value y)
    (ρ.scaled_multiplier_pos η w τ t y) ?_ u hu
  rw [cartesianClippedPatch_eq_box]
  filter_upwards [ae_restrict_mem (openCoordinateBox_isOpen a b).measurableSet] with x hx
  exact allowedWeight_box_comparison ρ L 5 (by linarith) (by norm_num) hLip a b hpos hBS h hh hwidth
    w τ t η hη hm hx hy

/-- The paper's B.2 inequality, with the actual L² difference and the actual
weak-gradient difference written explicitly. -/
theorem allowed_weight_cartesianKuhn_approximation
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
      (hTS : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ S) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → h*w.q t ≤ 1 →
      ∀ u : WeakSobolevJet (d+1) 2
        (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
        (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      WeakSobolevJet.value u ∈ dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) →
      let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
      σ.seminorm (WeakSobolevJet.value u-cartesianKuhnProjectionLp o δ hδ N (WeakSobolevJet.value u))+
        h*σ.seminorm (WeakSobolevJet.field ⟨1,by omega⟩ u-
          WeakSobolevJet.field ⟨1,by omega⟩ (cartesianKuhnProjectionJet o δ hδ N (WeakSobolevJet.value u))) ≤
        C*h^2*σ.seminorm (WeakSobolevJet.field 2 u) := by
  obtain ⟨C,hC,hbound⟩ := allowed_weight_cartesianKuhn_h2_error hS hc hcompact ρ hρ κ hκ
  refine ⟨C,hC,?_⟩
  intro o δ hδ N hTS h hh hlower hupper w τ t η hη hm u hu
  have he := hbound o δ hδ N hTS h hh hlower hupper w τ t η hη hm u hu
  dsimp only at he ⊢
  have hv : WeakSobolevJet.value
      (cartesianKuhnErrorJet o δ hδ N (WeakSobolevJet.truncate (by omega : 1 ≤ 2) u))=
      WeakSobolevJet.value u-cartesianKuhnProjectionLp o δ hδ N (WeakSobolevJet.value u) := by
    rw [cartesianKuhnErrorJet,map_sub,WeakSobolevJet.truncate_value,cartesianKuhnProjectionJet_value]
  rw [hv] at he
  exact he

end Carleman
