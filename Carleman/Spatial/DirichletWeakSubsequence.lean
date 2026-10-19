module

public import Carleman.Spatial.HilbertWeakSubsequence
public import Carleman.Spatial.DirichletSpace
public import Carleman.Spatial.SobolevHilbert
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! The original H¹₀ space is retained under a bounded weak subsequence.
Both actual L² derivative fields converge weakly along the same extraction. -/
@[expose] public noncomputable section
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_dirichlet_weak_subsequence
    (U : ℕ → WeakSobolevJet d 1 (volume.restrict S) S)
    (hU : ∀ n, U n ∈ dirichletJetSpace S) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ‖WeakSobolevJet.field 0 (U n)‖^2 + ‖WeakSobolevJet.field 1 (U n)‖^2 ≤ C^2) :
    ∃ u : WeakSobolevJet d 1 (volume.restrict S) S, u ∈ dirichletJetSpace S ∧
      ‖WeakSobolevJet.field 0 u‖^2 + ‖WeakSobolevJet.field 1 u‖^2 ≤ C^2 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ (k : Fin 2) (z : Lp (DerivativeFiber d k.val) 2 (volume.restrict S)),
        Tendsto (fun n => inner ℝ (WeakSobolevJet.field k (U (φ n))) z)
          atTop (𝓝 (inner ℝ (WeakSobolevJet.field k u) z)) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let H := SobolevHilbert d 1 (volume.restrict S) S
  let : SecondCountableTopology (HilbertJetFields d 1 (volume.restrict S)) := inferInstance
  let : TopologicalSpace.SeparableSpace H := inferInstance
  let K : Submodule ℝ H := (dirichletJetSpace S).comap SobolevHilbert.toJet.toLinearMap
  have hK : IsClosed (K : Set H) :=
    (Submodule.isClosed_topologicalClosure _).preimage SobolevHilbert.toJet.continuous
  have hn (n : ℕ) : ‖SobolevHilbert.ofJet (U n)‖ ≤ C := by
    have he : ‖SobolevHilbert.ofJet (U n)‖^2 =
        ‖WeakSobolevJet.field 0 (U n)‖^2 + ‖WeakSobolevJet.field 1 (U n)‖^2 := by
      have hh := SobolevHilbert.norm_sq (SobolevHilbert.ofJet (U n))
      change ‖SobolevHilbert.ofJet (U n)‖^2 = ∑ k : Fin 2, ‖WeakSobolevJet.field k (U n)‖^2 at hh
      rw [Fin.sum_univ_two] at hh
      exact hh
    have he' : ‖SobolevHilbert.ofJet (U n)‖^2 ≤ C^2 := he.trans_le (hb n)
    exact (sq_le_sq₀ (norm_nonneg _) hC).mp he'
  obtain ⟨v,hv,hvn,φ,hφ,ht⟩ := exists_hilbert_weak_subsequence_in_subspace K hK
    (fun n => SobolevHilbert.ofJet (U n)) hU hn
  refine ⟨SobolevHilbert.toJet v,hv,?_,φ,hφ,?_⟩
  · have he := SobolevHilbert.norm_sq v
    change ‖v‖^2 = ∑ k : Fin 2, ‖WeakSobolevJet.field k (SobolevHilbert.toJet v)‖^2 at he
    rw [Fin.sum_univ_two] at he
    rw [← he]
    exact pow_le_pow_left₀ (norm_nonneg _) hvn 2
  · intro k z
    exact hilbert_weak_tendsto_map ht ((WeakSobolevJet.fieldCLM k).comp SobolevHilbert.toJet) z

end Carleman
