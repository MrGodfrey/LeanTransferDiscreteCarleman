module

public import Carleman.Transfer.Comparison

/-!
# The finite B4 weight family

The errors are the actual differences U−R_h z̄. The energy norm is the sum
of all weighted spatial gradient squares. The B4 estimates only become
available after the auxiliary discrete equation is supplied; it is derived
from the original state equation using the already proved B2 theorem.
-/
@[expose] public noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Carleman
variable {H X F Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  {V D : Submodule ℝ H} {a : CarlemanExponents}

structure ErrorBridge (p : TransferGeometry V X F Y a) (g : TimeGrid)
    (r : Reconstruction V X) (l : LoadInterface r F)
    (A : D →ₗ[ℝ] H) (Ah : X →ₗ[ℝ] X) (hDV : D ≤ V)
    (s : Orientation) (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X)
    (u : PeriodicWeakTrajectory g D A) (errors : ErrorScales) (K τ : ℝ) : Prop where
  order : ∀ j, timeSq g p.weight.q (a.c j) (p.derivative j) (p.error g hDV u r s z) ≤
    K * p.graphSq g (a.energyPower j) (p.error g hDV u r s z)
  energy : s.difference g z + r.shiftedSpatial g Ah μ z =
      g.map r.J (l.transferLoad g μ f z) →
    ∀ j, a.energyPower j / 2 ≤ τ →
      p.graphSq g (a.energyPower j) (p.error g hDV u r s z) ≤
        K * errors.energy g ^ 2 * g.powerSq (p.weight.nodes g) (a.energyPower j)
          (p.node g p.space) (l.transferLoad g μ f z)
  l2 : s.difference g z + r.shiftedSpatial g Ah μ z =
      g.map r.J (l.transferLoad g μ f z) →
    ∀ b, b = a.c₀ ∨ b = a.o ∨ b = (4 * a.m : ℝ) → b / 2 ≤ τ →
      timeSq g p.weight.q b p.space (fun t => (p.error g hDV u r s z t : H)) ≤
        K * errors.l2 g ^ 2 * g.powerSq (p.weight.nodes g) b
          (p.node g p.space) (l.transferLoad g μ f z)
  shift : timeSq g p.weight.q 0 p.space
      (fun t => s.extension g μ t • (p.error g hDV u r s z t : H)) ≤
    K * timeSq g p.weight.q (4 * a.m : ℝ) p.space (fun t => (p.error g hDV u r s z t : H))
  finite_l2 : ∀ b, b = a.c₀ ∨ b = a.o ∨ b = (4 * a.m : ℝ) →
    TimeSquareIntegrable g p.weight.q b p.space
      (fun t => (p.error g hDV u r s z t : H))
  finite_energy : ∀ j (k : Fin (a.m + 1)),
    TimeSquareIntegrable g p.weight.q (2 * (a.m - k.val : ℕ) + a.energyPower j)
      (p.gradient k) (p.error g hDV u r s z)

namespace ErrorBridge
variable {p : TransferGeometry V X F Y a} {g : TimeGrid}
  {r : Reconstruction V X} {l : LoadInterface r F} {A : D →ₗ[ℝ] H}
  {Ah : X →ₗ[ℝ] X} {hDV : D ≤ V} {s : Orientation}
  {μ : g.Sequence ℝ} {f : g.Sequence F} {z : g.Sequence X}
  {u : PeriodicWeakTrajectory g D A} {errors : ErrorScales} {K τ : ℝ}
  (b : ErrorBridge p g r l A Ah hDV s μ f z u errors K τ)

include b in
theorem derivative_bound (hK : 0 ≤ K)
    (hcover : max (a.dStar / 2) (a.bStar / 2) ≤ τ)
    (hz : s.difference g z + g.map Ah z = fun i => l.Γ (f i)) :
    p.derivativeError g (p.error g hDV u r s z) ≤
      a.m * K ^ 2 * errors.energy g ^ 2 * g.powerSq (p.weight.nodes g) a.dStar
        (p.node g p.space) (l.transferLoad g μ f z) := by
  have hs := s.state_solves_shifted g l Ah μ f z hz
  have hc := a.weight_coverage hcover
  have hj : ∀ j, timeSq g p.weight.q (a.c j) (p.derivative j) (p.error g hDV u r s z) ≤
      K ^ 2 * errors.energy g ^ 2 * g.powerSq (p.weight.nodes g) a.dStar
        (p.node g p.space) (l.transferLoad g μ f z) := by
    intro j
    have he := b.energy hs j (hc.1 j)
    have hp := g.powerSq_mono_exponent (p.weight.nodes g) (fun _ => p.weight.lower _)
      (a.energyPower_le_dStar j) (p.node g p.space) (l.transferLoad g μ f z)
    have hh := (b.order j).trans (mul_le_mul_of_nonneg_left he hK)
    have hp' := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ K ^ 2 * errors.energy g ^ 2)
    nlinarith only [hh, hp']
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j
  simpa only [TransferGeometry.derivativeError, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_assoc] using hsum

include b in
theorem lower_bound (hK : 0 ≤ K)
    (hcover : max (a.dStar / 2) (a.bStar / 2) ≤ τ)
    (hz : s.difference g z + g.map Ah z = fun i => l.Γ (f i)) :
    p.lowerErrors g s μ (p.error g hDV u r s z) ≤
      (2 * K + K ^ 2) * errors.l2 g ^ 2 * g.powerSq (p.weight.nodes g) a.bStar
        (p.node g p.space) (l.transferLoad g μ f z) := by
  have hs := s.state_solves_shifted g l Ah μ f z hz
  have hc := a.weight_coverage hcover
  let e := p.error g hDV u r s z
  let G := g.powerSq (p.weight.nodes g) a.bStar (p.node g p.space) (l.transferLoad g μ f z)
  have hbound (j : ℝ) (hj : j = a.c₀ ∨ j = a.o ∨ j = (4 * a.m : ℝ))
      (hjτ : j / 2 ≤ τ) (hjb : j ≤ a.bStar) :
      timeSq g p.weight.q j p.space (fun t => (e t : H)) ≤ K * errors.l2 g ^ 2 * G := by
    have hp := g.powerSq_mono_exponent (p.weight.nodes g) (fun _ => p.weight.lower _)
      hjb (p.node g p.space) (l.transferLoad g μ f z)
    exact (b.l2 hs j hj hjτ).trans (mul_le_mul_of_nonneg_left hp (by positivity))
  have h₀ := hbound a.c₀ (Or.inl rfl) hc.2.1 a.c₀_le_bStar
  have ho := hbound a.o (Or.inr (Or.inl rfl)) hc.2.2.1 a.o_le_bStar
  have hm := hbound (4 * a.m) (Or.inr (Or.inr rfl)) (by linarith [hc.2.2.2]) a.four_m_le_bStar
  have hobs : timeSq g p.weight.q a.o p.observation (fun t => (e t : H)) ≤
      timeSq g p.weight.q a.o p.space (fun t => (e t : H)) := by
    have hh := timeSq_le g p.weight.q p.weight.nonneg a.o p.observation p.space
      (fun t => (e t : H)) (fun t => (e t : H)) (b.finite_l2 a.o (Or.inr (Or.inl rfl))) 1
      (Filter.Eventually.of_forall fun t => by
        have hn := apply_nonneg (p.observation t) (e t : H)
        have h := p.observation_le t (e t : H)
        have hn' := apply_nonneg (p.space t) (e t : H)
        nlinarith)
    simpa only [one_mul] using hh
  have hshift := b.shift.trans (mul_le_mul_of_nonneg_left hm hK)
  change _ + _ + _ ≤ _
  nlinarith only [h₀, ho, hobs, hshift]

include b in
theorem total_bound (hK : 1 ≤ K)
    (hcover : max (a.dStar / 2) (a.bStar / 2) ≤ τ)
    (hz : s.difference g z + g.map Ah z = fun i => l.Γ (f i)) :
    p.derivativeError g (p.error g hDV u r s z) + p.lowerErrors g s μ (p.error g hDV u r s z) ≤
      ((a.m : ℝ) + 3) * K ^ 2 *
        (errors.energy g ^ 2 * g.powerSq (p.weight.nodes g) a.dStar (p.node g p.space) (l.transferLoad g μ f z) +
         errors.l2 g ^ 2 * g.powerSq (p.weight.nodes g) a.bStar (p.node g p.space) (l.transferLoad g μ f z)) := by
  have hKn := zero_le_one.trans hK
  have hd := b.derivative_bound hKn hcover hz
  have hl := b.lower_bound hKn hcover hz
  have hnD := mul_nonneg (sq_nonneg (errors.energy g))
    (g.powerSq_nonneg (p.weight.nodes g) (fun _ => p.weight.nonneg _) a.dStar
      (p.node g p.space) (l.transferLoad g μ f z))
  have hnB := mul_nonneg (sq_nonneg (errors.l2 g))
    (g.powerSq_nonneg (p.weight.nodes g) (fun _ => p.weight.nonneg _) a.bStar
      (p.node g p.space) (l.transferLoad g μ f z))
  have hM : (0 : ℝ) ≤ a.m := Nat.cast_nonneg _
  have hKK : 2*K + K^2 ≤ ((a.m : ℝ)+3)*K^2 := by
    nlinarith [mul_nonneg hM (sq_nonneg K)]
  have hmD : (a.m : ℝ)*K^2 ≤ ((a.m : ℝ)+3)*K^2 := by nlinarith [sq_nonneg K]
  have h1 := mul_le_mul_of_nonneg_right hKK hnB
  have h2 := mul_le_mul_of_nonneg_right hmD hnD
  nlinarith only [hd, hl, h1, h2]

end ErrorBridge
end Carleman
