module

public import Carleman.Transfer.ErrorBridge

/-!
# Conditional Section 5 transfer

The common bridge bound K and the fixed order m determine all constants
before choosing the time grid, q, state, load or direction. The theorem
uses actual node and integral norms, derives B2, applies the exact finite B4
weight family, and proves B5. It is conditional on B1/B3/B4, not Theorem 2.1.
-/
@[expose] public noncomputable section
namespace Carleman

/-- Uniform comparison coefficient; no time-period parameter. -/
def comparisonConstant (K : ℝ) : ℝ := 2*K + 4*K^2 + 4*K^3
/-- Uniform coefficient after combining the two exact defect budgets. -/
def transferConstant (a : CarlemanExponents) (K : ℝ) : ℝ :=
  comparisonConstant K * (1 + 2 * ((a.m : ℝ) + 3) * K^4)

theorem transferConstant_pos (a : CarlemanExponents) {K : ℝ} (hK : 1 ≤ K) :
    0 < transferConstant a K := by
  have hk : 0 < K := zero_lt_one.trans_le hK
  unfold transferConstant comparisonConstant
  positivity

variable {H X F Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  {V D : Submodule ℝ H} {a : CarlemanExponents}
  {p : TransferGeometry V X F Y a} {g : TimeGrid}
  {r : Reconstruction V X} {l : LoadInterface r F} {A : D →ₗ[ℝ] H}
  {Ah : X →ₗ[ℝ] X} {hDV : D ≤ V} {s : Orientation}
  {Bstar : X →ₗ[ℝ] Y} {f : g.Sequence F} {z : g.Sequence X}
  {u : PeriodicWeakTrajectory g D A} {errors : ErrorScales} {K τ L : ℝ}

/-- The actual Section 5 pre-absorption estimate, with the paper's Λ_f and Λ_z. -/
theorem conditional_transfer_defect
    (hK : 1 ≤ K) (hL : L ^ (4*a.m) ≤ K)
    (hcover : max (a.dStar/2) (a.bStar/2) ≤ τ)
    (hR : ∀ i x, (p.space (g.nodeTime i) (r.RH x))^2 ≤ K * (p.state (g.nodeTime i) x)^2)
    (hLift : ∀ i v, (p.space (g.nodeTime i) (l.lift v))^2 ≤ K * (p.load (g.nodeTime i) v)^2)
    (bc : ComparisonBridge p g r l A hDV Bstar s (frozenShift a p.weight g L) f z u K)
    (be : ErrorBridge p g r l A Ah hDV s (frozenShift a p.weight g L) f z u errors K τ)
    (hz : s.difference g z + g.map Ah z = fun i => l.Γ (f i)) :
    p.nodeEnergy g r z ≤ transferConstant a K *
      ((1 + errors.loadDefect g a p.weight.max) * p.loadSq g f +
       p.observationSq g Bstar z + errors.stateDefect g a p.weight.max * p.nodeEnergy g r z) := by
  let μ := frozenShift a p.weight g L
  let e := p.error g hDV u r s z
  let Fq := p.loadSq g f
  let Oq := p.observationSq g Bstar z
  let E := p.nodeEnergy g r z
  let C₀ := comparisonConstant K
  let C₁ := 2 * ((a.m : ℝ)+3) * K^4
  have hKn : 0 ≤ K := zero_le_one.trans hK
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀, comparisonConstant]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hF : 0 ≤ Fq := g.weightedSq_nonneg _ _
  have hO : 0 ≤ Oq := g.powerSq_nonneg _ (fun _ => p.weight.nonneg _) _ _ _
  have hE : 0 ≤ E := p.nodeEnergy_nonneg g r z
  have hload (t : ℝ) (ht : 0 ≤ t) :
      g.powerSq (p.weight.nodes g) t (p.node g p.space) (l.transferLoad g μ f z) ≤
      2*K^2*(p.weight.max^t * Fq + max 1 (p.weight.max^(4*a.m+t-a.c₀))*E) := by
    have h := l.transferLoad_powerSq_le g p.weight a K hK
      (p.node g p.space) (p.node g p.state) (p.node g p.load) μ
      (frozenShift_sq_le a p.weight g L K hL) hR hLift t ht f z
    have hzero := p.zeroth_le_nodeEnergy g r z
    have hh := mul_le_mul_of_nonneg_left hzero
      (by positivity : 0 ≤ 2*K^2*max 1 (p.weight.max^(4*a.m+t-a.c₀)))
    dsimp only [Fq, E, TransferGeometry.loadSq]
    nlinarith only [h, hh]
  have hd := mul_le_mul_of_nonneg_left (hload a.dStar a.dStar_nonneg) (sq_nonneg (errors.energy g))
  have hb := mul_le_mul_of_nonneg_left (hload a.bStar a.bStar_nonneg) (sq_nonneg (errors.l2 g))
  have herr := be.total_bound hK hcover hz
  have hbudget : p.derivativeError g e + p.lowerErrors g s μ e ≤
      C₁ * (errors.loadDefect g a p.weight.max * Fq + errors.stateDefect g a p.weight.max * E) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hd hb)
      (by positivity : 0 ≤ ((a.m : ℝ)+3)*K^2)
    dsimp only [C₁, ErrorScales.loadDefect, ErrorScales.stateDefect]
    nlinarith only [herr, hh]
  have hcmp := bc.comparison hK
  have hcb := mul_le_mul_of_nonneg_left hbudget hC₀
  have hdef : 0 ≤ errors.loadDefect g a p.weight.max := by
    dsimp [ErrorScales.loadDefect]
    apply add_nonneg <;> apply mul_nonneg (sq_nonneg _) <;>
      exact Real.rpow_nonneg (zero_le_one.trans p.weight.max_ge_one) _
  have hzdef : 0 ≤ errors.stateDefect g a p.weight.max := by
    dsimp [ErrorScales.stateDefect]
    positivity
  have hFO := mul_nonneg (mul_nonneg hC₀ hC₁) (add_nonneg hF hO)
  have hDE := mul_nonneg hC₀
    (add_nonneg (mul_nonneg hdef hF) (mul_nonneg hzdef hE))
  change E ≤ _
  change E ≤ C₀ * (Fq + Oq + p.derivativeError g e + p.lowerErrors g s μ e) at hcmp
  change E ≤ C₀ * (1 + C₁) * ((1 + errors.loadDefect g a p.weight.max)*Fq + Oq +
    errors.stateDefect g a p.weight.max*E)
  nlinarith only [hcmp, hcb, hFO, hDE]

/-- B5: choose c_* only after the common constant, then obtain the load version. -/
theorem conditional_transfer_load
    (hK : 1 ≤ K) (hL : L ^ (4*a.m) ≤ K)
    (hcover : max (a.dStar/2) (a.bStar/2) ≤ τ)
    (hR : ∀ i x, (p.space (g.nodeTime i) (r.RH x))^2 ≤ K * (p.state (g.nodeTime i) x)^2)
    (hLift : ∀ i v, (p.space (g.nodeTime i) (l.lift v))^2 ≤ K * (p.load (g.nodeTime i) v)^2)
    (bc : ComparisonBridge p g r l A hDV Bstar s (frozenShift a p.weight g L) f z u K)
    (be : ErrorBridge p g r l A Ah hDV s (frozenShift a p.weight g L) f z u errors K τ)
    (hz : s.difference g z + g.map Ah z = fun i => l.Γ (f i))
    (hf : errors.loadDefect g a p.weight.max ≤ 1)
    (hs : errors.stateDefect g a p.weight.max ≤ 1 / (2 * transferConstant a K)) :
    p.nodeEnergy g r z ≤ 4 * transferConstant a K *
      (p.loadSq g f + p.observationSq g Bstar z) := by
  have hc := transferConstant_pos a hK
  have h := conditional_transfer_defect hK hL hcover hR hLift bc be hz
  have hF := g.weightedSq_nonneg (p.node g p.load) f
  have hO := g.powerSq_nonneg (p.weight.nodes g) (fun _ => p.weight.nonneg _)
    a.o (p.node g p.control) (fun i => Bstar (z i))
  have hE := p.nodeEnergy_nonneg g r z
  have hsf : transferConstant a K * errors.stateDefect g a p.weight.max ≤ 1/2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hc)).mp hs
    nlinarith only [hh]
  have hhf := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hf hF) hc.le
  have hhs := mul_le_mul_of_nonneg_right hsf hE
  have hhO := mul_nonneg hc.le hO
  dsimp only [TransferGeometry.loadSq, TransferGeometry.observationSq] at h ⊢
  nlinarith only [h, hhf, hhs, hhO]

end Carleman

@[expose] public noncomputable section
namespace Carleman
variable {H X F Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  {V D : Submodule ℝ H} {a : CarlemanExponents}

/-- B1/B3/B4 for every full state and either sign, at one common constant K.
No discrete conclusion is a field. The source theorem must eventually provide
this package uniformly over all admissible parameters from (A1)–(A4)/(N1)–(N5). -/
structure TransferBridges (p : TransferGeometry V X F Y a) (g : TimeGrid)
    (r : Reconstruction V X) (l : LoadInterface r F) (A : D →ₗ[ℝ] H)
    (Ah : X →ₗ[ℝ] X) (hDV : D ≤ V) (Bstar : X →ₗ[ℝ] Y)
    (errors : ErrorScales) (K τ L : ℝ) : Prop where
  shift_lower : 1 ≤ L
  shift_bound : L ^ (4*a.m) ≤ K
  coverage : max (a.dStar/2) (a.bStar/2) ≤ τ
  reconstruction_bound : ∀ i x,
    (p.space (g.nodeTime i) (r.RH x))^2 ≤ K * (p.state (g.nodeTime i) x)^2
  lift_bound : ∀ i v,
    (p.space (g.nodeTime i) (l.lift v))^2 ≤ K * (p.load (g.nodeTime i) v)^2
  solutions : ∀ (s : Orientation) (f : g.Sequence F) (z : g.Sequence X),
    s.difference g z + g.map Ah z = (fun i => l.Γ (f i)) →
    ∃ u : PeriodicWeakTrajectory g D A,
      ComparisonBridge p g r l A hDV Bstar s (frozenShift a p.weight g L) f z u K ∧
      ErrorBridge p g r l A Ah hDV s (frozenShift a p.weight g L) f z u errors K τ

namespace TransferBridges
variable {p : TransferGeometry V X F Y a} {g : TimeGrid}
  {r : Reconstruction V X} {l : LoadInterface r F} {A : D →ₗ[ℝ] H}
  {Ah : X →ₗ[ℝ] X} {hDV : D ≤ V} {Bstar : X →ₗ[ℝ] Y}
  {errors : ErrorScales} {K τ L : ℝ}
  (b : TransferBridges p g r l A Ah hDV Bstar errors K τ L)

include b in
theorem load_estimate (hK : 1 ≤ K)
    (hf : errors.loadDefect g a p.weight.max ≤ 1)
    (hs : errors.stateDefect g a p.weight.max ≤ 1 / (2 * transferConstant a K))
    (s : Orientation) (f : g.Sequence F) (z : g.Sequence X)
    (hz : s.difference g z + g.map Ah z = fun i => l.Γ (f i)) :
    p.nodeEnergy g r z ≤ 4 * transferConstant a K * (p.loadSq g f + p.observationSq g Bstar z) := by
  obtain ⟨u, bc, be⟩ := b.solutions s f z hz
  exact conditional_transfer_load hK b.shift_bound b.coverage b.reconstruction_bound
    b.lift_bound bc be hz hf hs

include b in
theorem residual_estimate (hK : 1 ≤ K)
    (hf : errors.loadDefect g a p.weight.max ≤ 1)
    (hs : errors.stateDefect g a p.weight.max ≤ 1 / (2 * transferConstant a K))
    (I : X → F) (hI : ∀ x, l.Γ (I x) = x)
    (hInorm : ∀ i x, (p.load (g.nodeTime i) (I x))^2 ≤ K * (p.state (g.nodeTime i) x)^2)
    (s : Orientation) (z : g.Sequence X) :
    p.nodeEnergy g r z ≤ 4 * transferConstant a K * K *
      (g.weightedSq (p.node g p.state) (s.difference g z + g.map Ah z) +
        p.observationSq g Bstar z) := by
  let residual := s.difference g z + g.map Ah z
  let f : g.Sequence F := fun i => I (residual i)
  have hz : s.difference g z + g.map Ah z = fun i => l.Γ (f i) :=
    (l.rightInverse_load g I hI residual).symm
  have h := b.load_estimate hK hf hs s f z hz
  have hload := g.weightedSq_le (p.node g p.load) (p.node g p.state) f residual
    (fun i => hInorm i (residual i))
  have hc := (transferConstant_pos a hK).le
  have hh := mul_le_mul_of_nonneg_left hload (by positivity : 0 ≤ 4*transferConstant a K)
  have ho := g.powerSq_nonneg (p.weight.nodes g) (fun _ => p.weight.nonneg _) a.o
    (p.node g p.control) (fun i => Bstar (z i))
  have hO := mul_nonneg (by positivity : 0 ≤ 4*transferConstant a K)
    (mul_nonneg (sub_nonneg.mpr hK) ho)
  dsimp only [TransferGeometry.loadSq, TransferGeometry.observationSq, residual] at h hh hO ⊢
  nlinarith only [h, hh, hO]

end TransferBridges

/-- Quantifier order makes T-uniformity explicit: c_* and C are chosen before
any grid or weight. Both conclusions hold for the entire discrete state space. -/
theorem conditional_transfer_uniform (a : CarlemanExponents) (K : ℝ) (hK : 1 ≤ K) :
    ∃ cStar > 0, ∃ C > 0,
      ∀ (g : TimeGrid) (p : TransferGeometry V X F Y a)
        (r : Reconstruction V X) (l : LoadInterface r F)
        (A : D →ₗ[ℝ] H) (Ah : X →ₗ[ℝ] X) (hDV : D ≤ V) (Bstar : X →ₗ[ℝ] Y)
        (errors : ErrorScales) (τ L : ℝ),
      TransferBridges p g r l A Ah hDV Bstar errors K τ L →
      errors.loadDefect g a p.weight.max ≤ 1 → errors.stateDefect g a p.weight.max ≤ cStar →
      (∀ (s : Orientation) (f : g.Sequence F) (z : g.Sequence X),
        s.difference g z + g.map Ah z = (fun i => l.Γ (f i)) →
        p.nodeEnergy g r z ≤ C * (p.loadSq g f + p.observationSq g Bstar z)) ∧
      (∀ (I : X → F), (∀ x, l.Γ (I x) = x) →
        (∀ i x, (p.load (g.nodeTime i) (I x))^2 ≤ K * (p.state (g.nodeTime i) x)^2) →
        ∀ (s : Orientation) (z : g.Sequence X),
          p.nodeEnergy g r z ≤ C *
            (g.weightedSq (p.node g p.state) (s.difference g z + g.map Ah z) +
              p.observationSq g Bstar z)) := by
  have hc := transferConstant_pos a hK
  have hk := zero_lt_one.trans_le hK
  refine ⟨1/(2*transferConstant a K), by positivity,
    4*transferConstant a K*K, by positivity, ?_⟩
  intro g p r l A Ah hDV Bstar errors τ L b hf hs
  constructor
  · intro s f z hz
    have h := b.load_estimate hK hf hs s f z hz
    have hF := g.weightedSq_nonneg (p.node g p.load) f
    have hO := g.powerSq_nonneg (p.weight.nodes g) (fun _ => p.weight.nonneg _) a.o
      (p.node g p.control) (fun i => Bstar (z i))
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity : 0 ≤ 4*transferConstant a K) hK)
      (add_nonneg hF hO))
  · intro I hI hInorm s z
    exact b.residual_estimate hK hf hs I hI hInorm s z

end Carleman
