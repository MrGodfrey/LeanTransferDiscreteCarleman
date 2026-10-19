module

public import Carleman.Spatial.PoissonExtensionComposition
public import Carleman.Geometry.ExpandedCoordinateBox

/-! Finite iteration through both faces of each coordinate. The enlarged
box and the norm constant are fixed before the original state is chosen. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem exists_finite_box_extension (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i)
    (s : Finset (Fin d))
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b))
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (hf : IsWeakNegativeLaplacian u f) :
    ∃ v g, IsPoissonExtension (expandedBox_contains a b s) ((4:ℝ)^s.card) u f v g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty,pow_zero]
    exact ⟨u,f,IsPoissonExtension.refl u hu f hf⟩
  | @insert r s hr ih =>
    obtain ⟨v,g,hv⟩ := ih
    let A := expandedBoxLower a b s
    let B := expandedBoxUpper a b s
    have hp : ∀ i, A i < B i := expandedBox_positive a b hpos s
    obtain ⟨v₁,g₁,h₁⟩ := exists_lower_box_extension A B hp v hv.1 g hv.2.1 r
    let A₁ := Function.update A r (2*A r-B r)
    have hp₁ : ∀ i, A₁ i < B i := by
      intro i
      by_cases hi : i=r
      · subst i; dsimp [A₁]; rw [Function.update_self]; linarith [hp r]
      · simpa only [A₁,Function.update_of_ne hi] using hp i
    obtain ⟨v₂,g₂,h₂⟩ := exists_upper_box_extension A₁ B hp₁ v₁ h₁.1 g₁ h₁.2.1 r
    have ht := (hv.trans (by norm_num : (0:ℝ) ≤ 2) h₁).trans (by norm_num : (0:ℝ) ≤ 2) h₂
    have hL : A₁=expandedBoxLower a b (insert r s) := expandedBoxLower_insert a b s r hr
    have hU : Function.update B r (2*B r-A₁ r)=expandedBoxUpper a b (insert r s) := by
      rw [hL]
      exact expandedBoxUpper_insert a b s r hr
    change ∃ v' g', IsPoissonExtension _ _ u f v' g'
    have hconst : (2:ℝ)*(2*4^s.card)=4^(insert r s).card := by
      rw [Finset.card_insert_of_notMem hr,pow_succ]
      ring
    rw [hconst] at ht
    have transport : ∀ (T' : Set (SpatialCoordinates d)), upperReflectedBox A₁ B r=T' →
        ∀ hST' : openCoordinateBox a b ⊆ T',
          ∃ v' g', IsPoissonExtension hST' (4^(insert r s).card) u f v' g' := by
      intro T' he hST'
      subst T'
      exact ⟨v₂,g₂,ht⟩
    apply transport _ _ _
    unfold upperReflectedBox
    rw [hU,hL]

end Carleman
