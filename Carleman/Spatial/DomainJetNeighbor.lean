module

public import Carleman.Spatial.DomainCoordinateInterpolation
public import Carleman.Spatial.FullSpaceJetInterpolation

/-! A uniform neighbor-order estimate for all actual symmetric weak jets on
a bounded Lipschitz domain. Component maxima are only a finite proof device. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem boundedLipschitz_jet_neighbor {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hS : IsBoundedLipschitzDomain S F) :
    ∃ δ K : ℝ, 0 < δ ∧ 1 ≤ K ∧ ∀ n : ℕ,
      ∀ u : WeakSobolevJet d n ((volume : Measure (SpatialCoordinates d)).restrict S) S,
      ∀ k : ℕ, 0 < k → k < n → ∀ t : ℝ, 0 < t → t ≤ δ →
      (WeakSobolevJet.componentMaximum u k : ℝ) ≤
        K*((WeakSobolevJet.componentMaximum u (k-1) : ℝ)/t+
          t*(WeakSobolevJet.componentMaximum u (k+1) : ℝ)) := by
  classical
  obtain ⟨P,_,_,hc,_⟩ := hS.finite_uniform_cones
  obtain ⟨δ,hδ,hd⟩ := finite_cones_common_height P
  obtain ⟨K,hK,hbound⟩ := finite_cones_coordinate_interpolation hS.isOpen P
    (subset_closure.trans hc) hδ hd
  refine ⟨δ,K,hδ,hK,?_⟩
  intro n u k hk hkn t ht htd
  have hnonneg : 0 ≤ K*((WeakSobolevJet.componentMaximum u (k-1) : ℝ)/t+
      t*(WeakSobolevJet.componentMaximum u (k+1) : ℝ)) := by positivity
  by_cases hz : WeakSobolevJet.componentMaximum u k = 0
  · simpa only [hz,NNReal.coe_zero] using hnonneg
  have hp : (0 : ℝ≥0) < WeakSobolevJet.componentMaximum u k := lt_of_le_of_ne zero_le (Ne.symm hz)
  unfold WeakSobolevJet.componentMaximum at hp
  rw [dite_eq_left (show k ≤ n by omega)] at hp
  obtain ⟨α,_,hα⟩ := (Finset.le_sup_iff hp).mp le_rfl
  have hm : (WeakSobolevJet.componentMaximum u k : ℝ) ≤
      ‖derivativeComponent α (WeakSobolevJet.field ⟨k,by omega⟩ u)‖ := by
    unfold WeakSobolevJet.componentMaximum
    rw [dite_eq_left (show k ≤ n by omega)]
    exact_mod_cast hα
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨i,α,rfl⟩ := Sym.exists_eq_cons_of_succ α
  let a := derivativeComponent α (WeakSobolevJet.field ⟨j,by omega⟩ u)
  let v := fun i => derivativeComponent (Sym.cons i α) (WeakSobolevJet.field ⟨j+1,by omega⟩ u)
  let w := fun i l => derivativeComponent (Sym.cons l (Sym.cons i α))
    (WeakSobolevJet.field ⟨j+2,by omega⟩ u)
  have he := hbound t ht htd a v w
    (fun i => WeakSobolevJet.field_weak_derivative u ⟨j,by omega⟩ α i)
    (fun i l => WeakSobolevJet.field_weak_derivative u ⟨j+1,by omega⟩ (Sym.cons i α) l)
    (WeakSobolevJet.componentMaximum u (j+2) : ℝ) (NNReal.coe_nonneg _)
    (fun i l => WeakSobolevJet.component_le_maximum u (j+2) (by omega) (Sym.cons l (Sym.cons i α))) i
  have ha := WeakSobolevJet.component_le_maximum u j (by omega) α
  apply (hm.trans he).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right ha ht.le) le_rfl) (zero_le_one.trans hK)
end Carleman
