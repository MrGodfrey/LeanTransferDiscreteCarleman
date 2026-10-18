module

public import Carleman.Spatial.DomainJetNeighbor
public import Carleman.Spatial.DiscreteInterpolation

/-! Parameter interpolation on the original bounded Lipschitz domain, for
all weak Sobolev jets of arbitrary finite order. One constant is fixed before
the parameter and state. No extension or interpolation estimate is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace Carleman
variable {d n : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace WeakSobolevJet

theorem boundedLipschitz_scaled_components (hS : IsBoundedLipschitzDomain S F) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      ∀ u : WeakSobolevJet d n ((volume : Measure (SpatialCoordinates d)).restrict S) S,
      ∀ k : ℕ, k ≤ n → r^(n-k)*(componentMaximum u k : ℝ) ≤
        C*(‖u‖+r^n*‖value u‖) := by
  obtain ⟨δ,K,hδ,hK,hneighbor⟩ := boundedLipschitz_jet_neighbor hS
  obtain ⟨C,hC,hmax⟩ := discrete_interpolation_maximum n hδ hK
  refine ⟨C,hC,?_⟩
  intro r hr u k hk
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  let x := fun j => r^(n-j)*(componentMaximum u j : ℝ)
  have hx (j : ℕ) : 0 ≤ x j := mul_nonneg (pow_nonneg hr0.le _) (NNReal.coe_nonneg _)
  have hb : ∀ j, 0 < j → j < n → ∀ t : ℝ, 0 < t → t ≤ δ →
      x j ≤ K*(x (j-1)/t+t*x (j+1)) := by
    intro j hj hjn t ht htd
    have hsmall : t/r ≤ δ := (div_le_self ht.le hr).trans htd
    have he := hneighbor n u j hj hjn (t/r) (div_pos ht hr0) hsmall
    have hprev : n-(j-1) = (n-j)+1 := by omega
    have hnow : n-j = (n-(j+1))+1 := by omega
    calc
      _ ≤ r^(n-j)*(K*((componentMaximum u (j-1) : ℝ)/(t/r)+
          (t/r)*(componentMaximum u (j+1) : ℝ))) :=
        mul_le_mul_of_nonneg_left he (pow_nonneg hr0.le _)
      _ = K*(x (j-1)/t+t*x (j+1)) := by
        dsimp [x]
        simp only [hprev,hnow,pow_succ]
        field_simp
  have he := hmax x hx hb k hk
  have hn := (componentMaximum_le_field u n le_rfl).trans (norm_field_le _ u)
  have he0 : x 0 = r^n*‖value u‖ := by simp only [x,Nat.sub_zero,componentMaximum_zero]
  have hen : x n = (componentMaximum u n : ℝ) := by simp only [x,Nat.sub_self,pow_zero,one_mul]
  rw [he0,hen] at he
  exact he.trans (mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans hC))

theorem boundedLipschitz_parameter_interpolation (hS : IsBoundedLipschitzDomain S F) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      ∀ u : WeakSobolevJet d n ((volume : Measure (SpatialCoordinates d)).restrict S) S,
      (∑ k : Fin (n+1), r^(n-k.val)*‖field k u‖) ≤ C*(‖u‖+r^n*‖value u‖) := by
  obtain ⟨C,hC,hbound⟩ := boundedLipschitz_scaled_components hS n
  let A := ∑ k : Fin (n+1), Real.sqrt (Fintype.card (Sym (Fin d) k.val))
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  refine ⟨1+A*C,by nlinarith,?_⟩
  intro r hr u
  have hB : 0 ≤ ‖u‖+r^n*‖value u‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg (zero_le_one.trans hr) _) (norm_nonneg _))
  have hsum : (∑ k : Fin (n+1), r^(n-k.val)*‖field k u‖) ≤ A*(C*(‖u‖+r^n*‖value u‖)) := by
    rw [show A = ∑ k : Fin (n+1), Real.sqrt (Fintype.card (Sym (Fin d) k.val)) from rfl,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    apply derivativeField_scaled_bound _ (pow_nonneg (zero_le_one.trans hr) _)
      (mul_nonneg (zero_le_one.trans hC) hB)
    intro α
    exact (mul_le_mul_of_nonneg_left (component_le_maximum u k.val (by omega) α)
      (pow_nonneg (zero_le_one.trans hr) _)).trans (hbound r hr u k.val (by omega))
  nlinarith
end WeakSobolevJet
end Carleman
