module

public import Carleman.Transfer.Geometry

/-! B1/B3 and (A4) imply Section 5's comparison on the actual normed objects. -/
@[expose] public noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Carleman
variable {H X F Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  {V D : Submodule ℝ H} {a : CarlemanExponents}

/-- Only primitive norm comparisons; the Section 5 comparison is proved below. -/
structure ComparisonBridge (p : TransferGeometry V X F Y a) (g : TimeGrid)
    (r : Reconstruction V X) (l : LoadInterface r F) (A : D →ₗ[ℝ] H)
    (hDV : D ≤ V) (Bstar : X →ₗ[ℝ] Y) (s : Orientation)
    (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X)
    (u : PeriodicWeakTrajectory g D A) (K : ℝ) : Prop where
  frozen : ∀ᵐ t ∂g.timeMeasure,
    s.sign • u.derivative t + A (u.domainValue t) + s.extension g μ t • u.value t =
      s.extension g (l.transferLoad g μ f z) t
  carleman : p.continuousEnergy g (p.trajectory g hDV u) ≤ K *
    (timeSq g p.weight.q 0 p.space (fun t => s.sign • u.derivative t + A (u.domainValue t)) +
     timeSq g p.weight.q a.o p.observation (fun t => (u.domainValue t : H)))
  node_state : g.powerSq (p.weight.nodes g) a.c₀ (p.node g p.state) z ≤
    K * timeSq g p.weight.q a.c₀ p.space (fun t => r.RH (s.extension g z t))
  node_derivative : ∀ j, g.powerSq (p.weight.nodes g) (a.c j)
    (p.node g (p.derivative j)) (fun i => r.R (z i)) ≤
    K * timeSq g p.weight.q (a.c j) (p.derivative j) (p.reconstruction g r s z)
  lifted_load : timeSq g p.weight.q 0 p.space
    (s.extension g (fun i => l.lift (f i))) ≤ K * p.loadSq g f
  observed_reconstruction : timeSq g p.weight.q a.o p.observation
    (fun t => r.RH (s.extension g z t)) ≤ K * p.observationSq g Bstar z
  finite_residual : TimeSquareIntegrable g p.weight.q 0 p.space
    (fun t => s.sign • u.derivative t + A (u.domainValue t))
  finite_observed_value : TimeSquareIntegrable g p.weight.q a.o p.observation
    (fun t => (u.domainValue t : H))
  finite_reconstruction₀ : TimeSquareIntegrable g p.weight.q a.c₀ p.space
    (fun t => r.RH (s.extension g z t))
  finite_reconstructionD : ∀ j, TimeSquareIntegrable g p.weight.q (a.c j)
    (p.derivative j) (p.reconstruction g r s z)
  finite_value₀ : TimeSquareIntegrable g p.weight.q a.c₀ p.space
    (fun t => (u.domainValue t : H))
  finite_error₀ : TimeSquareIntegrable g p.weight.q a.c₀ p.space
    (fun t => (p.error g hDV u r s z t : H))
  finite_valueD : ∀ j, TimeSquareIntegrable g p.weight.q (a.c j) (p.derivative j)
    (p.trajectory g hDV u)
  finite_errorD : ∀ j, TimeSquareIntegrable g p.weight.q (a.c j) (p.derivative j)
    (p.error g hDV u r s z)
  finite_lift : TimeSquareIntegrable g p.weight.q 0 p.space
    (s.extension g (fun i => l.lift (f i)))
  finite_shift : TimeSquareIntegrable g p.weight.q 0 p.space
    (fun t => s.extension g μ t • (p.error g hDV u r s z t : H))
  finite_observed_reconstruction : TimeSquareIntegrable g p.weight.q a.o p.observation
    (fun t => r.RH (s.extension g z t))
  finite_observed_error : TimeSquareIntegrable g p.weight.q a.o p.observation
    (fun t => -(p.error g hDV u r s z t : H))

namespace ComparisonBridge
variable {p : TransferGeometry V X F Y a} {g : TimeGrid}
  {r : Reconstruction V X} {l : LoadInterface r F} {A : D →ₗ[ℝ] H}
  {hDV : D ≤ V} {Bstar : X →ₗ[ℝ] Y} {s : Orientation}
  {μ : g.Sequence ℝ} {f : g.Sequence F} {z : g.Sequence X}
  {u : PeriodicWeakTrajectory g D A} {K : ℝ}
  (b : ComparisonBridge p g r l A hDV Bstar s μ f z u K)

include b in
theorem comparison (hK : 1 ≤ K) :
    p.nodeEnergy g r z ≤ (2 * K + 4 * K ^ 2 + 4 * K ^ 3) *
      (p.loadSq g f + p.observationSq g Bstar z +
        p.derivativeError g (p.error g hDV u r s z) +
        p.lowerErrors g s μ (p.error g hDV u r s z)) := by
  let v := p.trajectory g hDV u
  let Rz := p.reconstruction g r s z
  let e := p.error g hDV u r s z
  have hKn : 0 ≤ K := zero_le_one.trans hK
  have hnode : p.nodeEnergy g r z ≤ K * p.continuousEnergy g Rz := by
    have hd := Finset.sum_le_sum (s := Finset.univ) fun j _ => b.node_derivative j
    rw [← Finset.mul_sum] at hd
    exact (add_le_add b.node_state hd).trans_eq (by dsimp [TransferGeometry.continuousEnergy, Rz, TransferGeometry.reconstruction]; ring)
  have hsplit := p.continuousEnergy_sub_le g v e b.finite_value₀ b.finite_error₀
    b.finite_valueD b.finite_errorD
  have hve : v - e = Rz := by dsimp [v, e, Rz, TransferGeometry.error]; abel
  rw [hve] at hsplit
  have hres := u.residual_ae l s μ f z b.frozen
  have hres' : (fun t => s.sign • u.derivative t + A (u.domainValue t)) =ᵐ[g.timeMeasure]
      (s.extension g (fun i => l.lift (f i))) - (fun t => s.extension g μ t • (e t : H)) := by
    filter_upwards [hres, u.domainValue_ae] with t ht heq
    rw [← heq] at ht
    exact ht
  have hresSq := timeSq_sub_le g p.weight.q p.weight.nonneg 0 p.space
    (s.extension g (fun i => l.lift (f i))) (fun t => s.extension g μ t • (e t : H))
    b.finite_lift b.finite_shift
  rw [← timeSq_congr_ae g p.weight.q 0 p.space hres'] at hresSq
  have hobs := timeSq_sub_le g p.weight.q p.weight.nonneg a.o p.observation
    (fun t => r.RH (s.extension g z t)) (fun t => -(e t : H))
    b.finite_observed_reconstruction b.finite_observed_error
  have hobs_eq : (fun t => r.RH (s.extension g z t)) - (fun t => -(e t : H)) =
      (fun t => (u.domainValue t : H)) := by
    funext t
    dsimp [e, TransferGeometry.error, TransferGeometry.trajectory,
      TransferGeometry.reconstruction, Reconstruction.RH]
    abel
  rw [hobs_eq] at hobs
  have hneg : timeSq g p.weight.q a.o p.observation (fun t => -(e t : H)) =
      timeSq g p.weight.q a.o p.observation (fun t => (e t : H)) := by
    simp only [timeSq, timeDensity, map_neg_eq_map]
  rw [hneg] at hobs
  have hcombined := hnode.trans (mul_le_mul_of_nonneg_left hsplit hKn)
  have hCE := mul_le_mul_of_nonneg_left b.carleman (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hKn)
  have hRS := mul_le_mul_of_nonneg_left hresSq (by positivity : 0 ≤ 2 * K ^ 2)
  have hOS := mul_le_mul_of_nonneg_left hobs (by positivity : 0 ≤ 2 * K ^ 2)
  have hLF := mul_le_mul_of_nonneg_left b.lifted_load (by positivity : 0 ≤ 4 * K ^ 2)
  have hOR := mul_le_mul_of_nonneg_left b.observed_reconstruction (by positivity : 0 ≤ 4 * K ^ 2)
  have hF := g.weightedSq_nonneg (p.node g p.load) f
  have hO := g.powerSq_nonneg (p.weight.nodes g) (fun _ => p.weight.nonneg _) a.o
    (p.node g p.control) (fun i => Bstar (z i))
  have hE₀ := timeSq_nonneg g p.weight.q p.weight.nonneg a.c₀ p.space (fun t => (e t : H))
  have hEO := timeSq_nonneg g p.weight.q p.weight.nonneg a.o p.observation (fun t => (e t : H))
  have hES := timeSq_nonneg g p.weight.q p.weight.nonneg 0 p.space
    (fun t => s.extension g μ t • (e t : H))
  have hED : 0 ≤ p.derivativeError g e :=
    Finset.sum_nonneg fun j _ => timeSq_nonneg g p.weight.q p.weight.nonneg (a.c j) (p.derivative j) e
  have hfinal : p.nodeEnergy g r z ≤
      4 * K ^ 3 * (p.loadSq g f + p.observationSq g Bstar z) +
      2 * K * (timeSq g p.weight.q a.c₀ p.space (fun t => (e t : H)) + p.derivativeError g e) +
      4 * K ^ 2 * (timeSq g p.weight.q a.o p.observation (fun t => (e t : H)) +
        timeSq g p.weight.q 0 p.space (fun t => s.extension g μ t • (e t : H))) := by
    dsimp only [TransferGeometry.continuousEnergy] at hcombined hCE
    change _ ≤ _ at hcombined
    dsimp only [v] at hcombined
    dsimp only [TransferGeometry.derivativeError]
    nlinarith only [hcombined, hCE, hRS, hOS, hLF, hOR]
  change _ ≤ (2 * K + 4 * K ^ 2 + 4 * K ^ 3) *
    (p.loadSq g f + p.observationSq g Bstar z + p.derivativeError g e + p.lowerErrors g s μ e)
  unfold TransferGeometry.lowerErrors
  have hFO : 0 ≤ p.loadSq g f + p.observationSq g Bstar z := add_nonneg hF hO
  have hEE : 0 ≤ timeSq g p.weight.q a.c₀ p.space (fun t => (e t : H)) + p.derivativeError g e := add_nonneg hE₀ hED
  have hOO : 0 ≤ timeSq g p.weight.q a.o p.observation (fun t => (e t : H)) +
      timeSq g p.weight.q 0 p.space (fun t => s.extension g μ t • (e t : H)) := add_nonneg hEO hES
  nlinarith [mul_nonneg (by positivity : 0 ≤ 2*K + 4*K^2) hFO,
    mul_nonneg (by positivity : 0 ≤ 4*K^2 + 4*K^3) hEE,
    mul_nonneg (by positivity : 0 ≤ 2*K + 4*K^3) hOO]

end ComparisonBridge
end Carleman
