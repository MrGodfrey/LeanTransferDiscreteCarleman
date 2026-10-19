module

public import Carleman.Spatial.BoxPoissonExtensionValue
public import Carleman.Spatial.FiniteBoxPoissonExtension
public import Carleman.Spatial.DoubleOddSlab

/-! Full finite Poisson extension, retaining local oddness at every original face. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem exists_finite_odd_box_extension (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i)
    (s : Finset (Fin d))
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b))
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (hf : IsWeakNegativeLaplacian u f) :
    ∃ v g, IsPoissonExtension (expandedBox_contains a b s) ((4:ℝ)^s.card) u f v g ∧
      ∀ r ∈ s,
        IsOddInSlab (zeroExtendLp (openCoordinateBox_isOpen _ _).measurableSet
          (WeakSobolevJet.value v)) r (a r) (b r-a r) ∧
        IsOddInSlab (zeroExtendLp (openCoordinateBox_isOpen _ _).measurableSet
          (WeakSobolevJet.value v)) r (b r) (b r-a r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty,pow_zero]
    exact ⟨u,f,IsPoissonExtension.refl u hu f hf,by simp⟩
  | @insert r s hr ih =>
    obtain ⟨v,g,hv,ho⟩ := ih
    let A := expandedBoxLower a b s
    let B := expandedBoxUpper a b s
    have hp : ∀ i, A i < B i := expandedBox_positive a b hpos s
    have hAr : A r=a r := by simp [A,expandedBoxLower,hr]
    have hBr : B r=b r := by simp [B,expandedBoxUpper,hr]
    obtain ⟨v₁,g₁,h₁,he₁⟩ := exists_lower_box_extension_value A B hp v hv.1 g hv.2.1 r
    let A₁ := Function.update A r (2*A r-B r)
    have hp₁ : ∀ i, A₁ i < B i := by
      intro i
      by_cases hi : i=r
      · subst i; dsimp [A₁]; rw [Function.update_self]; linarith [hp r]
      · simpa only [A₁,Function.update_of_ne hi] using hp i
    obtain ⟨v₂,g₂,h₂,he₂⟩ := exists_upper_box_extension_value A₁ B hp₁ v₁ h₁.1 g₁ h₁.2.1 r
    have he := he₂.trans (congrArg (coordinateOddPart r (B r)) he₁)
    have ht := (hv.trans (by norm_num : (0:ℝ) ≤ 2) h₁).trans (by norm_num : (0:ℝ) ≤ 2) h₂
    have hconst : (2:ℝ)*(2*4^s.card)=4^(insert r s).card := by
      rw [Finset.card_insert_of_notMem hr,pow_succ]; ring
    rw [hconst] at ht
    have hodd : ∀ j ∈ insert r s,
        IsOddInSlab (zeroExtendLp (openCoordinateBox_isOpen _ _).measurableSet
          (WeakSobolevJet.value v₂)) j (a j) (b j-a j) ∧
        IsOddInSlab (zeroExtendLp (openCoordinateBox_isOpen _ _).measurableSet
          (WeakSobolevJet.value v₂)) j (b j) (b j-a j) := by
      intro j hj
      rw [he]
      rcases Finset.mem_insert.mp hj with he | hj
      · subst j
        have hz := zeroExtend_box_zero_outside_slab A B (WeakSobolevJet.value v) r
        have hh := double_oddPart_both_faces (hp r) hz
        simpa only [hAr,hBr] using hh
      · have hjr : j ≠ r := by intro he; subst j; exact hr hj
        exact ⟨((ho j hj).1.oddPart_other r (A r) hjr).oddPart_other r (B r) hjr,
          ((ho j hj).2.oddPart_other r (A r) hjr).oddPart_other r (B r) hjr⟩
    have hL : A₁=expandedBoxLower a b (insert r s) := expandedBoxLower_insert a b s r hr
    have hU : Function.update B r (2*B r-A₁ r)=expandedBoxUpper a b (insert r s) := by
      rw [hL]; exact expandedBoxUpper_insert a b s r hr
    have transport : ∀ (T' : Set (SpatialCoordinates d)), upperReflectedBox A₁ B r=T' →
        ∀ (hT' : IsOpen T') (hST' : openCoordinateBox a b ⊆ T'),
          ∃ v' g', IsPoissonExtension hST' (4^(insert r s).card) u f v' g' ∧
            ∀ j ∈ insert r s,
              IsOddInSlab (zeroExtendLp hT'.measurableSet (WeakSobolevJet.value v')) j (a j) (b j-a j) ∧
              IsOddInSlab (zeroExtendLp hT'.measurableSet (WeakSobolevJet.value v')) j (b j) (b j-a j) := by
      intro T' he hT' hST'
      subst T'
      exact ⟨v₂,g₂,ht,hodd⟩
    apply transport _ _ (openCoordinateBox_isOpen _ _) _
    unfold upperReflectedBox
    rw [hU,hL]

end Carleman
