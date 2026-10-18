module

public import Carleman.Weights.LipschitzShiftSobolev
public import Carleman.Weights.LipschitzEulerSobolev
public import Carleman.Weights.LipschitzFrozenSobolev
public import Carleman.Weights.LipschitzTemporalError
public import Carleman.Weights.AllowedFormBounds

/-! Full original Section 3 conclusions expressed with the genuine cyclic
sequence, periodic Sobolev graph and weak spatial derivative fields. Every
solution of the equation is covered, not only a chosen constructed solution. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section3
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 ν) W)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hDV : b.domain ≤ V) (hD : b.domain ≤ sobolevSubspace d (2*m) ν S)

/-- Lemma 3.3: full-domain existence/uniqueness and the actual nodal R norm. -/
def EulerEstimate (g : TimeGrid) (s : Orientation) (w : TimeWeight)
    (ρ : SpatialProfile ν) (L τ K : ℝ) : Prop :=
  ∀ f : g.Sequence (Lp ℝ 2 ν),
    (∃! u : g.Sequence b.domain, b.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u = f) ∧
    ∀ u : g.Sequence b.domain,
      b.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u = f →
      g.l2Norm (ρ.nodeMap g w τ (s.difference g (fun i => (u i : Lp ℝ 2 ν)))) +
        WeakSobolevJet.nodeParameterNorm g (w.nodes g)
          (fun i => ρ.multiplier w τ (g.nodeTime i)) (fun i => domainSobolevJet hS hν hD (u i)) ≤
        K*g.l2Norm (ρ.nodeMap g w τ f)

/-- Lemmas 3.1/3.4 for the specified actual continuous multiplier. Graph
membership carries an H weak derivative, a.e. D(A), and periodic H traces. -/
def ContinuousEstimate (g : TimeGrid) (s : Orientation) (w : TimeWeight)
    (ρ : SpatialProfile ν) (τ K : ℝ) (hq : AEStronglyMeasurable w.q g.timeMeasure)
    (μ : BoundedMultiplier g.timeMeasure) : Prop :=
  ∀ f : Lp (Lp ℝ 2 ν) 2 g.timeMeasure,
    (∃! p : b.PeriodicGraph g, b.evolution g s μ p = f) ∧
    ∀ p : b.PeriodicGraph g, b.evolution g s μ p = f →
      MemLp (fun t => domainSobolevJet hS hν hD (p.toTrajectory.domainValue t)) 2 g.timeMeasure ∧
      ‖ρ.timeMap g w τ hq p.val.2.1‖ +
        WeakSobolevJet.spacetimeParameterNorm g w.q (ρ.multiplier w τ)
          (fun t => domainSobolevJet hS hν hD (p.toTrajectory.domainValue t)) ≤
        K*‖ρ.timeMap g w τ hq f‖

/-- Theorem 3.5 with the same orientation for the equation and cell extension,
for arbitrary original discrete and continuous solutions and their real error. -/
def TemporalEstimate (g : TimeGrid) (s : Orientation) (w : TimeWeight)
    (ρ : SpatialProfile ν) (L τ K : ℝ) : Prop :=
  ∀ (f : g.Sequence (Lp ℝ 2 ν)) (u : g.Sequence b.domain) (p : b.PeriodicGraph g),
    b.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u = f →
    b.evolution g s (s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))) p = s.extensionLp g f →
    bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
      (p.toTrajectory.value t-s.extension g (fun i => (u i : Lp ℝ 2 ν)) t)) ≤
        K*g.dt*g.l2Norm (ρ.nodeMap g w τ f) ∧
    MemLp (fun t => domainSobolevJet hS hν hV
      (b.domain.inclusion hDV (p.toTrajectory.domainError s u t))) 2 g.timeMeasure ∧
    WeakSobolevJet.spacetimeWeightedNorm g w.q (ρ.multiplier w τ)
      (fun t => domainSobolevJet hS hν hV (b.domain.inclusion hDV (p.toTrajectory.domainError s u t))) ≤
        K*Real.sqrt g.dt*g.l2Norm (ρ.nodeMap g w τ f)

omit [CompleteSpace W] in
theorem EulerEstimate.mono {g : TimeGrid} {s : Orientation} {w : TimeWeight} {ρ : SpatialProfile ν} {L τ K K' : ℝ}
    (h : EulerEstimate hS hν b hD g s w ρ L τ K) (hK : K ≤ K') :
    EulerEstimate hS hν b hD g s w ρ L τ K' := by
  intro f
  refine ⟨(h f).1,fun u hu => ((h f).2 u hu).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hK (g.l2Norm_nonneg _)

theorem ContinuousEstimate.mono {g : TimeGrid} {s : Orientation} {w : TimeWeight} {ρ : SpatialProfile ν} {τ K K' : ℝ}
    {hq : AEStronglyMeasurable w.q g.timeMeasure} {μ : BoundedMultiplier g.timeMeasure}
    (h : ContinuousEstimate hS hν b hD g s w ρ τ K hq μ) (hK : K ≤ K') :
    ContinuousEstimate hS hν b hD g s w ρ τ K' hq μ := by
  intro f
  refine ⟨(h f).1,?_⟩
  intro p hp
  exact ⟨((h f).2 p hp).1,(((h f).2 p hp).2).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))⟩

theorem TemporalEstimate.mono {g : TimeGrid} {s : Orientation} {w : TimeWeight} {ρ : SpatialProfile ν} {L τ K K' : ℝ}
    (h : TemporalEstimate hS hν b hV hDV g s w ρ L τ K) (hK : K ≤ K') :
    TemporalEstimate hS hν b hV hDV g s w ρ L τ K' := by
  intro f u p hu hp
  obtain ⟨h1,h2,h3⟩ := h f u p hu hp
  refine ⟨h1.trans ?_,h2,h3.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK g.dt_pos.le) (g.l2Norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg _)) (g.l2Norm_nonneg _)
end Carleman.Section3
