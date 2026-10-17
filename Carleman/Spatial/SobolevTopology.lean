module

public import Carleman.Spatial.SobolevRealization

/-! The genuine weak Sobolev jet is a closed subspace of the finite product
of its L² derivative fields. Its complete graph norm is the product norm,
not the norm induced by its image in scalar L². -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman

def derivativeComponentCLM {d k : ℕ} {ν : Measure (SpatialCoordinates d)}
    (α : Sym (Fin d) k) : Lp (DerivativeFiber d k) 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (OperatorMultiplier.const (EuclideanSpace.proj α)).continuousLinearMap

theorem derivativeComponentCLM_apply {d k : ℕ} {ν : Measure (SpatialCoordinates d)}
    (α : Sym (Fin d) k) (u : Lp (DerivativeFiber d k) 2 ν) :
    derivativeComponentCLM α u = derivativeComponent α u := rfl

/-- The distributional identities are closed equalities of continuous L² pairings. -/
theorem weakJetSubmodule_isClosed (d m : ℕ) (ν : Measure (SpatialCoordinates d))
    [IsFiniteMeasureOnCompacts ν] (S : Set (SpatialCoordinates d)) :
    IsClosed (weakJetSubmodule d m ν S : Set (JetFields d m ν)) := by
  change IsClosed {u : JetFields d m ν | ∀ (k : Fin m) (α : Sym (Fin d) k.val)
    (i : Fin d) (φ : SpatialTest S),
      inner ℝ (derivativeComponent α (u k.castSucc))
        (φ.derivativeLp ν (EuclideanSpace.basisFun (Fin d) ℝ i)) =
      -inner ℝ (derivativeComponent (Sym.cons i α) (u k.succ)) (φ.toLp ν)}
  simp only [ofPred_forall]
  refine isClosed_iInter fun k => isClosed_iInter fun α =>
    isClosed_iInter fun i => isClosed_iInter fun φ => ?_
  exact isClosed_eq
    (((derivativeComponentCLM α).continuous.comp (continuous_apply k.castSucc)).inner
      continuous_const)
    ((((derivativeComponentCLM (Sym.cons i α)).continuous.comp
      (continuous_apply k.succ)).inner continuous_const).neg)

instance weakSobolevJet_completeSpace (d m : ℕ) (ν : Measure (SpatialCoordinates d))
    [IsFiniteMeasureOnCompacts ν] (S : Set (SpatialCoordinates d)) :
    CompleteSpace (WeakSobolevJet d m ν S) := by
  let : IsClosed (weakJetSubmodule d m ν S : Set (JetFields d m ν)) :=
    weakJetSubmodule_isClosed d m ν S
  exact IsClosed.completeSpace_coe

namespace WeakSobolevJet
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

def fieldCLM (k : Fin (m+1)) :
    WeakSobolevJet d m ν S →L[ℝ] Lp (DerivativeFiber d k.val) 2 ν :=
  (ContinuousLinearMap.proj k).comp (weakJetSubmodule d m ν S).subtypeL

theorem fieldCLM_apply (k : Fin (m+1)) (u : WeakSobolevJet d m ν S) :
    fieldCLM k u = field k u := rfl

def valueCLM : WeakSobolevJet d m ν S →L[ℝ] Lp ℝ 2 ν :=
  (derivativeComponentCLM Sym.nil).comp (fieldCLM 0)

theorem valueCLM_apply (u : WeakSobolevJet d m ν S) : valueCLM u = value u := rfl

theorem norm_field_le (k : Fin (m+1)) (u : WeakSobolevJet d m ν S) :
    ‖field k u‖ ≤ ‖u‖ := norm_le_pi_norm (u : JetFields d m ν) k

/-- The complete product norm is equivalent to the sum of actual derivative L² norms. -/
theorem norm_le_sum_fields (u : WeakSobolevJet d m ν S) :
    ‖u‖ ≤ ∑ k : Fin (m+1), ‖field k u‖ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
  intro k
  exact Finset.single_le_sum (fun i _ => norm_nonneg (field i u)) (Finset.mem_univ k)

theorem sum_fields_le (u : WeakSobolevJet d m ν S) :
    (∑ k : Fin (m+1), ‖field k u‖) ≤ (m+1 : ℝ) * ‖u‖ := by
  calc
    _ ≤ ∑ _k : Fin (m+1), ‖u‖ := Finset.sum_le_sum fun k _ => norm_field_le k u
    _ = _ := by simp

/-- Bochner measurability of all actual derivatives follows from graph-space measurability. -/
theorem aestronglyMeasurable_field {μ : Measure ℝ} {u : ℝ → WeakSobolevJet d m ν S}
    (hu : AEStronglyMeasurable u μ) (k : Fin (m+1)) :
    AEStronglyMeasurable (fun t => field k (u t)) μ :=
  (fieldCLM k).continuous.comp_aestronglyMeasurable hu

/-- L² in the genuine complete graph space supplies each actual L² derivative in time. -/
theorem memLp_field {μ : Measure ℝ} {u : ℝ → WeakSobolevJet d m ν S}
    (hu : MemLp u 2 μ) (k : Fin (m+1)) : MemLp (fun t => field k (u t)) 2 μ := by
  apply hu.of_le_mul (c := 1) (aestronglyMeasurable_field hu.aestronglyMeasurable k)
  exact Filter.Eventually.of_forall fun t => by simpa using norm_field_le k (u t)

end WeakSobolevJet
end Carleman
