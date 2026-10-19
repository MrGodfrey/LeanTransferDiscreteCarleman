module

public import Carleman.Geometry.KuhnInverseMap
public import Carleman.Spatial.AffineSimplexInverse
public import Carleman.Geometry.FiniteCartesianKuhnCover

/-! Uniform genuine L² inverse estimates on every actual physical Kuhn
cell; the affine inverse-map bound is proved from the original grid steps. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem cartesianKuhn_uniform_inverse (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C > (0:ℝ), ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
      (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (h : ℝ), 0 < h →
      (∀ j, h/κ ≤ δ j) → ∀ c : Fin (d+1) → ℝ,
      ‖simplexNodalGradientLp (cartesianKuhnSimplex o δ hδ z π) c‖ ≤
        (C/h)*‖simplexNodalLp (cartesianKuhnSimplex o δ hδ z π) c‖ := by
  obtain ⟨C,hC,hbound⟩ := affineSimplex_inverse_uniform (kuhnReferenceSimplex d) κ hκ
  refine ⟨C,hC,?_⟩
  intro o δ hδ z π h hh hlower c
  exact hbound ((coordinatePermutation π).trans (coordinateDilation δ hδ))
    (WithLp.toLp 2 (fun j => o j+(z j:ℝ)*δ j)) h hh
    (cartesianKuhn_inverse_map_bound δ hδ π κ h hκ hh hlower) c

theorem cartesianFiniteSimplex_uniform_inverse (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C > (0:ℝ), ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
      (N : Fin d → ℕ) (i : CartesianCellIndex N) (h : ℝ), 0 < h →
      (∀ j, h/κ ≤ δ j) → ∀ c : Fin (d+1) → ℝ,
      ‖simplexNodalGradientLp (cartesianFiniteSimplex o δ hδ N i) c‖ ≤
        (C/h)*‖simplexNodalLp (cartesianFiniteSimplex o δ hδ N i) c‖ := by
  obtain ⟨C,hC,hbound⟩ := cartesianKuhn_uniform_inverse d κ hκ
  exact ⟨C,hC,fun o δ hδ N i h hh hlower c => hbound o δ hδ (cartesianCellLatticeIndex N i).1 i.2 h hh hlower c⟩

end Carleman
