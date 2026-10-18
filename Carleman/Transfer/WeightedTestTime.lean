module

public import Carleman.Periodic.TestOperatorDerivative
public import Carleman.Spatial.AllowedWeight

/-! N4's actual qσ reconstruction-mass derivative bound controls the negative
part of the periodic test pairing. The constant 18 C is uniform in T and qmax;
the final cell uses endpoint compatibility, for both time directions. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Carleman.SpatialProfile
variable {Ω X : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (ρ : SpatialProfile ν) {w : TimeWeight} {g : TimeGrid} {β : ℝ}
  (h : TimeWeightRegularity w g β) (τ τStar : ℝ) (hτ : |τ| ≤ τStar)
  (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
  (hmw : (4*β*(τStar+ρ.bound)) * g.dt * w.max ^ 2 ≤ 1)

include h hτ hm hmw

/-- Cell comparison of the precise mass norm in N4 and the A3 margin. -/
theorem test_mass_cell_le {s t : ℝ} (hs : s ∈ Icc 0 g.period)
    (ht : t ∈ Icc 0 g.period) (hd : |t-s| ≤ g.dt) (v : Lp ℝ 2 ν) :
    w.q t * (ρ.multiplier w τ t).seminorm v ≤
      6 * (w.q s * (ρ.multiplier w τ s).seminorm v) := by
  have hc := mul_le_mul (h.comparable hs ht hd hm).1
    (ρ.seminorm_cell_le h τ τStar hτ hs ht hd hm hmw v)
    (apply_nonneg _ _) (by positivity [w.nonneg s])
  convert hc using 1
  ring

/-- The continuous derivative estimate produces an actual closed-cell bound. -/
theorem test_derivative_cell_bound (R : X →ₗ[ℝ] Lp ℝ 2 ν)
    (T' : ℝ → X →ₗ[ℝ] X) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z t, t ∈ Icc 0 g.period →
      |inner ℝ z (T' t z)| ≤ C*(w.q t*(ρ.multiplier w τ t).seminorm (R z))^2)
    {s t : ℝ} (hs : s ∈ Icc 0 g.period) (ht : t ∈ Icc 0 g.period)
    (hd : |t-s| ≤ g.dt) (z : X) :
    |inner ℝ z (T' t z)| ≤ 36*C*(w.q s*(ρ.multiplier w τ s).seminorm (R z))^2 := by
  have hc := ρ.test_mass_cell_le h τ τStar hτ hm hmw hs ht hd (R z)
  have hn : 0 ≤ w.q t*(ρ.multiplier w τ t).seminorm (R z) :=
    mul_nonneg (w.nonneg t) (apply_nonneg _ _)
  have hs' : 0 ≤ 6*(w.q s*(ρ.multiplier w τ s).seminorm (R z)) :=
    mul_nonneg (by norm_num) (mul_nonneg (w.nonneg s) (apply_nonneg _ _))
  have he := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hn hs').mpr hc) hC
  exact (hb z t ht).trans (he.trans_eq (by ring))

/-- N4, actual allowed-weight cell comparison, and the exact time identity
imply the lower bound consumed by shifted coercivity; D+ uses the left node. -/
theorem pairing_test_dPlus_lower (R : X →ₗ[ℝ] Lp ℝ 2 ν)
    (T T' : ℝ → X →ₗ[ℝ] X) (hend : T 0 = T g.period)
    (hder : ∀ z t, t ∈ Icc 0 g.period →
      HasDerivWithinAt (fun x => inner ℝ z (T x z)) (inner ℝ z (T' t z))
        (Icc 0 g.period) t)
    (hsym : ∀ i v z, inner ℝ v (T (g.nodeTime i) z) = inner ℝ z (T (g.nodeTime i) v))
    (hpos : ∀ i z, 0 ≤ inner ℝ z (T (g.nodeTime i) z))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z t, t ∈ Icc 0 g.period →
      |inner ℝ z (T' t z)| ≤ C*(w.q t*(ρ.multiplier w τ t).seminorm (R z))^2)
    (u : g.Sequence X) :
    -(18*C)*(g.dt*∑ i, (w.q (g.nodeTime i)*
      (ρ.multiplier w τ (g.nodeTime i)).seminorm (R (u i)))^2) ≤
      g.pairing (g.dPlus u) (fun i => T (g.nodeTime i) (u i)) := by
  have he := g.pairing_testOperator_dPlus_lower T hend T' hder hsym hpos u
    (fun i => 36*C*(w.q (g.nodeTime i)*
      (ρ.multiplier w τ (g.nodeTime i)).seminorm (R (u i)))^2) (by
        intro i t ht
        have hl := (g.cellTime_mem i.val (Nat.le_of_lt i.isLt)).1
        have hr := (g.cellTime_mem (i.val+1) (Nat.succ_le_of_lt i.isLt)).2
        have hs : g.nodeTime i ∈ Icc 0 g.period := g.cellTime_mem i.val (Nat.le_of_lt i.isLt)
        have hd : |t-g.nodeTime i| ≤ g.dt := by
          have hlen := g.cellTime_succ_sub i.val
          change |t-g.cellTime i.val| ≤ g.dt
          rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
          linarith [ht.2]
        exact ρ.test_derivative_cell_bound h τ τStar hτ hm hmw R T' hC hb
          hs ⟨hl.trans ht.1, ht.2.trans hr⟩ hd (u i))
  simp only [← Finset.mul_sum] at he
  convert he using 1
  ring

/-- D− uses the right endpoint of the previous cell. At node zero this is
T, whose q and σ agree exactly with their values at zero. -/
theorem pairing_test_dMinus_lower (R : X →ₗ[ℝ] Lp ℝ 2 ν)
    (T T' : ℝ → X →ₗ[ℝ] X) (hend : T 0 = T g.period)
    (hder : ∀ z t, t ∈ Icc 0 g.period →
      HasDerivWithinAt (fun x => inner ℝ z (T x z)) (inner ℝ z (T' t z))
        (Icc 0 g.period) t)
    (hsym : ∀ i v z, inner ℝ v (T (g.nodeTime i) z) = inner ℝ z (T (g.nodeTime i) v))
    (hpos : ∀ i z, 0 ≤ inner ℝ z (T (g.nodeTime i) z))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z t, t ∈ Icc 0 g.period →
      |inner ℝ z (T' t z)| ≤ C*(w.q t*(ρ.multiplier w τ t).seminorm (R z))^2)
    (u : g.Sequence X) :
    -(18*C)*(g.dt*∑ i, (w.q (g.nodeTime i)*
      (ρ.multiplier w τ (g.nodeTime i)).seminorm (R (u i)))^2) ≤
      g.pairing (g.dMinus u) (fun i => T (g.nodeTime i) (u i)) := by
  have he := g.pairing_testOperator_dMinus_lower T hend T' hder hsym hpos u
    (fun i => 36*C*(w.q (g.nodeTime i)*
      (ρ.multiplier w τ (g.nodeTime i)).seminorm (R (u i)))^2) (by
        intro i t ht
        have hl := (g.cellTime_mem (g.prev i).val (Nat.le_of_lt (g.prev i).isLt)).1
        have hs := g.cellTime_mem ((g.prev i).val+1) (Nat.succ_le_of_lt (g.prev i).isLt)
        have hd : |t-g.cellTime ((g.prev i).val+1)| ≤ g.dt := by
          rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
          have hlen := g.cellTime_succ_sub (g.prev i).val
          linarith [ht.1]
        have hh := ρ.test_derivative_cell_bound h τ τStar hτ hm hmw R T' hC hb
          hs ⟨hl.trans ht.1, ht.2.trans hs.2⟩ hd (u i)
        have hmend : ρ.multiplier w τ 0 = ρ.multiplier w τ g.period := by
          simp only [multiplier, h.endpoint]
        rw [g.next_node_value w.q h.endpoint, g.next_node_value (ρ.multiplier w τ) hmend,
          g.next_prev] at hh
        exact hh)
  simp only [← Finset.mul_sum] at he
  convert he using 1
  ring

end Carleman.SpatialProfile
