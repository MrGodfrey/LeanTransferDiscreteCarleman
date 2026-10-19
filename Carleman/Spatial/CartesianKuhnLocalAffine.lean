module

public import Carleman.Geometry.CartesianClippedBoundary
public import Carleman.Spatial.CartesianKuhnAffineProjection
public import Carleman.Spatial.DirichletLocalAffine

/-! The original H²∩H¹₀ state supplies a physical-boundary-compatible
local affine approximant which the actual moment reconstruction reproduces. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman

theorem cartesianKuhnProjection_physical_affine {d : ℕ}
    (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
    (i : CartesianCellIndex N) (p : SpatialCoordinates (d+1) →ᵃ[ℝ] ℝ)
    (hp : ∀ f ∈ cartesianClippedPhysicalFaces o δ N i, ∀ y ∈
      coordinateClosedFace f.1 (cartesianClippedPatchLower o δ N i) (cartesianClippedPatchUpper o δ N i) f.2, p y=0)
    {x : SpatialCoordinates (d+1)} (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
    cartesianKuhnProjection o δ hδ N
      (boundedAffineLp (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j)) p) x=p x :=
  cartesianKuhnProjection_affine_on_cell o δ hδ N i p
    (fun k hk => cartesianPhysicalFace_zero_on_boundaryCell o δ hδ N i p hp
      (subset_convexHull ℝ _ (Set.mem_range_self k)) hk) hx

theorem cartesianKuhn_h2_local_reproduced_affine (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
      (i : CartesianCellIndex N) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
      ∀ u : WeakSobolevJet (d+1) 2
        (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
        (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      WeakSobolevJet.value u ∈ dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) →
      let a := cartesianClippedPatchLower o δ N i
      let b := cartesianClippedPatchUpper o δ N i
      ∃ (p : SpatialCoordinates (d+1) →ᵃ[ℝ] ℝ)
        (r : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)),
        (∀ f ∈ cartesianClippedPhysicalFaces o δ N i, ∀ y ∈ coordinateClosedFace f.1 a b f.2, p y=0) ∧
        (∀ x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
          cartesianKuhnProjection o δ hδ N
            (boundedAffineLp (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j)) p) x=p x) ∧
        (WeakSobolevJet.value r =ᵐ[volume.restrict (openCoordinateBox a b)]
          (fun x => WeakSobolevJet.value u x-p x)) ∧
        ‖WeakSobolevJet.value r‖+h*‖WeakSobolevJet.field 1 r‖ ≤
          C*h^2*bochnerL2Norm (volume.restrict (cartesianClippedPatch o δ N i)) (WeakSobolevJet.field 2 u) := by
  obtain ⟨C,hC,hbound⟩ := dirichlet_h2_local_boundary_affine d (5*κ) (by linarith)
  refine ⟨C,hC,?_⟩
  intro o δ hδ N i h hh hlower hupper u hu
  dsimp only
  let a := cartesianClippedPatchLower o δ N i
  let b := cartesianClippedPatchUpper o δ N i
  have hpos (j : Fin (d+1)) : a j < b j := by
    have hb := (cartesianClippedPatch_width_bounds o δ hδ N i j).1
    change δ j ≤ b j-a j at hb
    linarith [hδ j]
  have hBS : openCoordinateBox a b ⊆ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) := by
    rw [← cartesianClippedPatch_eq_box]
    exact cartesianClippedPatch_subset_domain o δ N i
  have hl (j : Fin (d+1)) : h/(5*κ) ≤ b j-a j := by
    have hk : 0 < κ := by linarith
    have he₁ : (h/(5*κ))*(5*κ)=h := div_mul_cancel₀ h (by positivity)
    have he₂ : (h/κ)*κ=h := div_mul_cancel₀ h hk.ne'
    have hd : h/(5*κ) ≤ h/κ := by nlinarith [div_nonneg hh.le hk.le]
    exact hd.trans ((hlower j).trans (cartesianClippedPatch_width_bounds o δ hδ N i j).1)
  have hupp (j : Fin (d+1)) : b j-a j ≤ (5*κ)*h := by
    have hb := (cartesianClippedPatch_width_bounds o δ hδ N i j).2
    change b j-a j ≤ 5*δ j at hb
    nlinarith [hupper j]
  obtain ⟨p,r,hp,hr,he⟩ := hbound _ (openCoordinateBox_isOpen _ _) a b hpos hBS h hh hl hupp
    (cartesianClippedPhysicalFaces o δ N i) (fun f hf => cartesianClippedPhysicalFaces_frontier o δ hδ N i f hf) u hu
  refine ⟨p,r,hp,fun x hx => cartesianKuhnProjection_physical_affine o δ hδ N i p hp hx,hr,?_⟩
  rw [subdomainLp_norm_eq_bochner] at he
  simpa only [cartesianClippedPatch_eq_box] using he

end Carleman
