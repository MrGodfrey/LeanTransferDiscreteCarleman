module

public import Carleman.Transfer.Weights

/-! Section 5, Step 4 for actual weighted auxiliary loads. -/
@[expose] public noncomputable section
namespace Carleman.LoadInterface
variable {H X F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F]
  {V : Submodule ℝ H} {r : Reconstruction V X}

/-- N1/N2 and the frozen shift give the two exact q-exponent losses. -/
theorem transferLoad_powerSq_le (l : LoadInterface r F) (g : TimeGrid)
    (w : TimeWeight) (a : CarlemanExponents) (K : ℝ) (hK : 1 ≤ K)
    (pH : g.Index → Seminorm ℝ H) (pX : g.Index → Seminorm ℝ X)
    (pF : g.Index → Seminorm ℝ F) (μ : g.Sequence ℝ)
    (hμ : ∀ i, μ i ^ 2 ≤ K * w.nodes g i ^ (4 * a.m : ℝ))
    (hR : ∀ i x, (pH i (r.RH x)) ^ 2 ≤ K * (pX i x) ^ 2)
    (hL : ∀ i f, (pH i (l.lift f)) ^ 2 ≤ K * (pF i f) ^ 2)
    (s : ℝ) (hs : 0 ≤ s) (f : g.Sequence F) (z : g.Sequence X) :
    g.powerSq (w.nodes g) s pH (l.transferLoad g μ f z) ≤
      2 * K ^ 2 * (w.max ^ s * g.weightedSq pF f +
        max 1 (w.max ^ (4 * a.m + s - a.c₀)) * g.powerSq (w.nodes g) a.c₀ pX z) := by
  let q := w.nodes g
  have hq : ∀ i, 1 ≤ q i := fun i => w.lower _
  have hqn : ∀ i, 0 ≤ q i := fun i => zero_le_one.trans (hq i)
  have hqp : ∀ i, 0 < q i := fun i => zero_lt_one.trans_le (hq i)
  have hQ : ∀ i, q i ≤ w.max := fun i => w.upper _
  have hKn : 0 ≤ K := zero_le_one.trans hK
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hload := g.powerSq_le q hqn s pH pF (fun i => l.lift (f i)) f (fun i => hL i (f i))
  have hload' := g.powerSq_le_max_pow q hq w.max hQ s hs pF f
  have hstate := g.powerSq_node_smul_le q hqp s (4 * a.m) pH μ
    (fun i => r.RH (z i)) hμ
  have hrec := g.powerSq_le q hqn (s + 4 * a.m) pH pX
    (fun i => r.RH (z i)) z (fun i => hR i (z i))
  have hpow := g.powerSq_change_exponent q hq w.max hQ (s + 4 * a.m) a.c₀ pX z
  rw [add_comm s (4 * a.m)] at hpow
  have hload_final : g.powerSq q s pH (fun i => l.lift (f i)) ≤
      K ^ 2 * (w.max ^ s * g.weightedSq pF f) :=
    hload.trans ((mul_le_mul_of_nonneg_left hload' hKn).trans
      (mul_le_mul_of_nonneg_right hKK
        (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans w.max_ge_one) s) (g.weightedSq_nonneg pF f))))
  have hstate_final : g.powerSq q s pH (fun i => μ i • r.RH (z i)) ≤
      K ^ 2 * (max 1 (w.max ^ (4 * a.m + s - a.c₀)) * g.powerSq q a.c₀ pX z) := by
    have hh := hstate.trans (mul_le_mul_of_nonneg_left hrec hKn)
    have hh' := mul_le_mul_of_nonneg_left hpow (sq_nonneg K)
    rw [add_comm s (4 * a.m)] at hh
    nlinarith only [hh, hh']
  have hadd := g.powerSq_add_le q hqn s pH (fun i => l.lift (f i))
    (fun i => μ i • r.RH (z i))
  change g.powerSq q s pH ((fun i => l.lift (f i)) + (fun i => μ i • r.RH (z i))) ≤ _
  nlinarith only [hadd, hload_final, hstate_final]

end Carleman.LoadInterface
