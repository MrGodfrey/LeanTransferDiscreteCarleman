module

public import Carleman.Weights.CellBounds

/-! A single uniform interface collecting every component of paper Lemma 3.2.
The local statements are stronger: they hold for any two times at distance at most dt.
For sigma choose r=rho(x) or r=-rho(x), with |r| <= R. -/
@[expose] public noncomputable section
open Set
namespace Carleman
open TimeWeightRegularity

structure CellEstimates (w : TimeWeight) (g : TimeGrid) (m : ℕ) (τStar R C : ℝ) : Prop where
  q_comparable : ∀ {s t : ℝ}, s ∈ Icc 0 g.period → t ∈ Icc 0 g.period → |t-s| ≤ g.dt →
    w.q t ≤ C*w.q s ∧ w.q s ≤ C*w.q t
  weight_comparable : ∀ τ r, |τ| ≤ τStar → |r| ≤ R → ∀ {s t : ℝ},
    s ∈ Icc 0 g.period → t ∈ Icc 0 g.period → |t-s| ≤ g.dt →
    allowedWeight (w := w) τ r t ≤ C*allowedWeight (w := w) τ r s ∧
    allowedWeight (w := w) τ r s ≤ C*allowedWeight (w := w) τ r t
  q_relative : ∀ o : Orientation, ∀ {t : ℝ}, t ∈ Icc 0 g.period →
    |w.q t / o.extension g (w.nodes g) t - 1| ≤ C*g.dt*o.extension g (w.nodes g) t
  weight_relative : ∀ o : Orientation, ∀ τ r, |τ| ≤ τStar → |r| ≤ R → ∀ {t : ℝ},
    t ∈ Icc 0 g.period →
    |allowedWeight (w := w) τ r t /
      o.extension g (fun i => allowedWeight (w := w) τ r (g.nodeTime i)) t - 1| ≤
        C*g.dt*(o.extension g (w.nodes g) t)^2
  shift_frozen : ∀ o : Orientation, ∀ L, 1 ≤ L → ∀ {t : ℝ}, t ∈ Icc 0 g.period →
    |(L*w.q t)^(2*m) - o.extension g (fun i => (L*w.nodes g i)^(2*m)) t| ≤
      C*L^(2*m)*g.dt*w.q t^(2*m+1)
  weight_quotient : ∀ τ r, |τ| ≤ τStar → |r| ≤ R → ∀ i : g.Index,
    |(allowedWeight (w := w) τ r (g.nodeTime i) /
      allowedWeight (w := w) τ r (g.nodeTime (g.prev i)) - 1) / g.dt| ≤ C*w.nodes g i^2
  shift_increment : ∀ L, 1 ≤ L → ∀ i : g.Index,
    |(L*w.nodes g (g.next i))^(2*m) - (L*w.nodes g i)^(2*m)| ≤
      C*L^(2*m)*g.dt*w.nodes g i^(2*m+1)

/-- Lemma 3.2: delta and C precede every period, weight, grid, L, orientation and node.
The paper additionally assumes dt <= 1 and C²/q'' bounds; this proof does not need them. -/
theorem cell_estimates_uniform (m : ℕ) (hm : 0 < m) (β τStar R : ℝ)
    (hβ : 0 < β) (hτ : 0 ≤ τStar) (hR : 0 ≤ R) :
    ∃ δ > 0, ∃ C > 0, ∀ (w : TimeWeight) (g : TimeGrid),
      TimeWeightRegularity w g β → g.dt*w.max^2 ≤ δ → CellEstimates w g m τStar R C := by
  let S : ℝ := 2*(2*m:ℕ)*2^(2*m-1)*β
  let C := max 3 (max (2*β) (max (8*β*(τStar+R)) (max (32*β*(τStar+R)) S)))
  have h3 : 3 ≤ C := le_max_left _ _
  have h2 : 2 ≤ C := by linarith
  have hq : 2*β ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hw : 8*β*(τStar+R) ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hH : 32*β*(τStar+R) ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hS : S ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨cellThreshold β τStar R, cellThreshold_pos hβ hτ hR, C, by linarith, ?_⟩
  intro w g h hmesh
  obtain ⟨hb, hbw⟩ := h.mesh_bounds τStar R hτ hR hmesh
  have hk : 1 ≤ 2*m := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t hs ht hd
    obtain ⟨hc, hc'⟩ := h.comparable hs ht hd hb
    exact ⟨hc.trans (mul_le_mul_of_nonneg_right h2 (w.nonneg s)),
      hc'.trans (mul_le_mul_of_nonneg_right h2 (w.nonneg t))⟩
  · intro τ r hτ' hr s t hs ht hd
    have hc := h.weight_le τ r τStar R hτ' hr hs ht hd hb hbw
    have hc' := h.weight_le τ r τStar R hτ' hr ht hs
      (by simpa only [abs_sub_comm] using hd) hb hbw
    exact ⟨hc.trans (mul_le_mul_of_nonneg_right h3 (allowedWeight_pos τ r s).le),
      hc'.trans (mul_le_mul_of_nonneg_right h3 (allowedWeight_pos τ r t).le)⟩
  · intro o t ht
    apply (h.relative_q_extension o ht hb).trans
    have hn : 0 ≤ o.extension g (w.nodes g) t := by
      rw [o.extension_eq_cellNumber]
      exact w.nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq g.dt_pos.le) hn
  · intro o τ r hτ' hr t ht
    exact (h.relative_weight_extension o τ r τStar R hτ' hr ht hb hbw).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw g.dt_pos.le) (sq_nonneg _))
  · intro o L hL t ht
    have hLn : 0 ≤ L := zero_le_one.trans hL
    exact (h.shift_extension o L hLn (2*m) hk ht hb).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS (pow_nonneg hLn _)) g.dt_pos.le)
        (pow_nonneg (w.nonneg t) _))
  · intro τ r hτ' hr i
    exact (h.weight_node_quotient τ r τStar R hτ' hr hb hbw i).trans
      (mul_le_mul_of_nonneg_right hH (sq_nonneg _))
  · intro L hL i
    have hLn : 0 ≤ L := zero_le_one.trans hL
    exact (h.shift_node_increment L hLn (2*m) hk hb i).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS (pow_nonneg hLn _)) g.dt_pos.le)
        (pow_nonneg (w.nonneg (g.nodeTime i)) _))

namespace CellEstimates
/-- The original H_n L-infinity statement follows on the actual observed spatial measure. -/
theorem weight_quotient_essSup {w : TimeWeight} {g : TimeGrid} {m : ℕ} {τStar R C : ℝ}
    (b : CellEstimates w g m τStar R C) {Ω : Type*} [MeasurableSpace Ω]
    (ν : MeasureTheory.Measure Ω) (ρ : Ω → ℝ) (τ : ℝ) (hτ : |τ| ≤ τStar)
    (hρ : ∀ᵐ x ∂ν, |ρ x| ≤ R) (i : g.Index) :
    MeasureTheory.eLpNormEssSup (fun x =>
      (allowedWeight (w := w) τ (ρ x) (g.nodeTime i) /
       allowedWeight (w := w) τ (ρ x) (g.nodeTime (g.prev i)) - 1) / g.dt) ν ≤
        ENNReal.ofReal (C*w.nodes g i^2) := by
  apply MeasureTheory.eLpNormEssSup_le_of_ae_bound
  filter_upwards [hρ] with x hx
  simpa only [Real.norm_eq_abs] using b.weight_quotient τ (ρ x) hτ hx i

/-- All real-time cells, using exactly the periodic extension stipulated in the paper.
The same C is retained across the period boundary; no new differentiability premise is used. -/
theorem global_cell_bounds {w : TimeWeight} {g : TimeGrid} {m : ℕ} {τStar R C : ℝ}
    (b : CellEstimates w g m τStar R C) (hper : Function.Periodic w.q g.period)
    (o : Orientation) (τ r L : ℝ) (hτ : |τ| ≤ τStar) (hr : |r| ≤ R) (hL : 1 ≤ L) (t : ℝ) :
    let qn := o.extension g (w.nodes g) t
    let sn := o.extension g (fun i => allowedWeight (w := w) τ r (g.nodeTime i)) t
    (w.q t ≤ C*qn ∧ qn ≤ C*w.q t) ∧
    (allowedWeight (w := w) τ r t ≤ C*sn ∧ sn ≤ C*allowedWeight (w := w) τ r t) ∧
    |w.q t/qn-1| ≤ C*g.dt*qn ∧
    |allowedWeight (w := w) τ r t/sn-1| ≤ C*g.dt*qn^2 ∧
    |(L*w.q t)^(2*m)-o.extension g (fun i => (L*w.nodes g i)^(2*m)) t| ≤
      C*L^(2*m)*g.dt*w.q t^(2*m+1) := by
  let qn := o.extension g (w.nodes g)
  let sn := o.extension g (fun i => allowedWeight (w := w) τ r (g.nodeTime i))
  let μn := o.extension g (fun i => (L*w.nodes g i)^(2*m))
  let f := fun x => (w.q x, qn x, sn x, μn x)
  have hp : Function.Periodic f g.period := by
    intro x
    dsimp only [f, qn, sn, μn]
    rw [hper x, o.extension_periodic g (w.nodes g) x,
      o.extension_periodic g (fun i => allowedWeight (w := w) τ r (g.nodeTime i)) x,
      o.extension_periodic g (fun i => (L*w.nodes g i)^(2*m)) x]
  obtain ⟨y, hy, he⟩ := hp.exists_mem_Ico₀ g.period_pos t
  have hy' : y ∈ Icc 0 g.period := ⟨hy.1, hy.2.le⟩
  dsimp only [f] at he
  obtain ⟨hq, hqn, hsn, hμn⟩ := (by simpa only [Prod.mk.injEq] using he :
    w.q t = w.q y ∧ qn t = qn y ∧ sn t = sn y ∧ μn t = μn y)
  have hσ : allowedWeight (w := w) τ r t = allowedWeight (w := w) τ r y := by
    simp only [allowedWeight, hq]
  change (w.q t ≤ C*qn t ∧ qn t ≤ C*w.q t) ∧
    (allowedWeight (w := w) τ r t ≤ C*sn t ∧ sn t ≤ C*allowedWeight (w := w) τ r t) ∧
    |w.q t/qn t-1| ≤ C*g.dt*qn t ∧
    |allowedWeight (w := w) τ r t/sn t-1| ≤ C*g.dt*(qn t)^2 ∧
    |(L*w.q t)^(2*m)-μn t| ≤ C*L^(2*m)*g.dt*w.q t^(2*m+1)
  rw [hq, hqn, hsn, hμn, hσ]
  have hend : w.q 0 = w.q g.period := by simpa only [zero_add] using (hper 0).symm
  have hsEnd : allowedWeight (w := w) τ r 0 = allowedWeight (w := w) τ r g.period := by
    simp only [allowedWeight, hend]
  have hqc := b.q_comparable (o.anchor_mem g hy') hy' (o.anchor_distance g y)
  rw [o.anchor_value_eq_extension g w.q hend hy'] at hqc
  have hsc := b.weight_comparable τ r hτ hr (o.anchor_mem g hy') hy' (o.anchor_distance g y)
  rw [o.anchor_value_eq_extension g _ hsEnd hy'] at hsc
  exact ⟨hqc, hsc, b.q_relative o hy', b.weight_relative o τ r hτ hr hy', b.shift_frozen o L hL hy'⟩

end CellEstimates

end Carleman
