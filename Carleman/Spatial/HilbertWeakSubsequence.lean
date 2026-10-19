module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.WeakDual

/-! Actual weak subsequences of bounded sequences in a separable Hilbert
space, with their uniform norm bound retained. -/
@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace Carleman

theorem exists_hilbert_weak_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (u : ℕ → H) {C : ℝ} (hb : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : H, ‖v‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ z : H, Tendsto (fun n => inner ℝ (u (φ n)) z) atTop (𝓝 (inner ℝ v z)) := by
  let U : ℕ → WeakDual ℝ H := fun n => StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ H) (u n))
  have hU (n : ℕ) : U n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) C := by
    change dist ((InnerProductSpace.toDual ℝ H) (u n)) 0 ≤ C
    simpa only [dist_zero_right,(InnerProductSpace.toDual ℝ H).norm_map] using hb n
  obtain ⟨v,hv,φ,hφ,ht⟩ := (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) C) hU
  let V := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual v)
  refine ⟨V,?_,φ,hφ,?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual v)‖ ≤ C
    rw [(InnerProductSpace.toDual ℝ H).symm.norm_map]
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hv
  · intro z
    have he := ((WeakDual.eval_continuous z).tendsto v).comp ht
    change Tendsto (fun n => inner ℝ (u (φ n)) z) atTop (𝓝 ((WeakDual.toStrongDual v) z)) at he
    simpa only [V,InnerProductSpace.toDual_symm_apply] using he


theorem exists_hilbert_weak_subsequence_in_subspace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (K : Submodule ℝ H) (hK : IsClosed (K : Set H))
    (u : ℕ → H) (hu : ∀ n, u n ∈ K) {C : ℝ} (hb : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : H, v ∈ K ∧ ‖v‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ z : H, Tendsto (fun n => inner ℝ (u (φ n)) z) atTop (𝓝 (inner ℝ v z)) := by
  let : IsClosed (K : Set H) := hK
  let : CompleteSpace K := IsClosed.completeSpace_coe
  obtain ⟨v,hv,φ,hφ,ht⟩ := exists_hilbert_weak_subsequence (fun n => (⟨u n,hu n⟩ : K)) hb
  refine ⟨v,v.property,hv,φ,hφ,?_⟩
  intro z
  simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using ht (K.orthogonalProjectionOnto z)

theorem hilbert_weak_tendsto_map
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    {u : ℕ → H} {v : H}
    (h : ∀ z : H, Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z)))
    (L : H →L[ℝ] G) (z : G) :
    Tendsto (fun n => inner ℝ (L (u n)) z) atTop (𝓝 (inner ℝ (L v) z)) := by
  simpa only [ContinuousLinearMap.adjoint_inner_right] using h (L.adjoint z)

end Carleman
