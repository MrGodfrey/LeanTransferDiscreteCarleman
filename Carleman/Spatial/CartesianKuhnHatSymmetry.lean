module

public import Carleman.Geometry.KuhnReflection

/-! Central symmetry of the actual finite-domain interior-node hats,
including nodes in the first and last interior grid layers. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnHat_reflection_of_nonzero (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (x : SpatialCoordinates d) (hx : cartesianKuhnHat o δ hδ N a x ≠ 0) :
    cartesianKuhnHat o δ hδ N a (AffineEquiv.pointReflection ℝ (cartesianGridPoint o δ a) x)=
      cartesianKuhnHat o δ hδ N a x := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp (cartesianKuhnHat_support_subset o δ hδ N a hx)
  by_cases hv : cartesianGridPoint o δ a ∈ Set.range (cartesianFiniteSimplex o δ hδ N i).points
  · rw [ite_eq_left hv] at hi
    obtain ⟨j,hj⟩ := cartesianFiniteSimplex_reflected_incident o δ hδ N a ha i hv
    obtain ⟨k,hk⟩ := hv
    have hvj : cartesianGridPoint o δ a=(cartesianFiniteSimplex o δ hδ N j).points k.rev := by
      have h := hj k
      rw [hk,AffineEquiv.pointReflection_self] at h
      exact h
    have hrx : AffineEquiv.pointReflection ℝ (cartesianGridPoint o δ a) x ∈
        simplicialCell (cartesianFiniteSimplex o δ hδ N j).points := by
      rw [← simplex_cell_affine_relabel _ _ _ Fin.revPerm hj]
      exact ⟨x,hi,rfl⟩
    rw [cartesianKuhnHat_on_incidentCell o δ hδ N a j k.rev hvj hrx,
      cartesianKuhnHat_on_incidentCell o δ hδ N a i k hk.symm hi]
    exact simplexBarycentric_affine_relabel _ _ _ Fin.revPerm hj k x
  · simp only [ite_eq_right hv,mem_empty_iff_false] at hi

theorem cartesianKuhnHat_reflection (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (x : SpatialCoordinates d) :
    cartesianKuhnHat o δ hδ N a (AffineEquiv.pointReflection ℝ (cartesianGridPoint o δ a) x)=
      cartesianKuhnHat o δ hδ N a x := by
  by_cases hx : cartesianKuhnHat o δ hδ N a x=0
  · by_cases hr : cartesianKuhnHat o δ hδ N a
        (AffineEquiv.pointReflection ℝ (cartesianGridPoint o δ a) x)=0
    · exact hr.trans hx.symm
    · have he := cartesianKuhnHat_reflection_of_nonzero o δ hδ N a ha _ hr
      rw [AffineEquiv.pointReflection_involutive ℝ (cartesianGridPoint o δ a) x,hx] at he
      exact (hr he.symm).elim
  · exact cartesianKuhnHat_reflection_of_nonzero o δ hδ N a ha x hx

end Carleman
