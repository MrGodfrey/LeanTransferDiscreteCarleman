module

public import Carleman.Control.ReconstructedControlCompactness

/-! Pointwise kernels as closed Bochner subspaces, preserved by true weak subsequences. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {H G Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [MeasurableSpace Ω]

def bochnerKernelSpace (L : H →L[ℝ] G) (μ : Measure Ω) : Submodule ℝ (Lp H 2 μ) :=
  (L.compLpL 2 μ).ker

omit [CompleteSpace H] in
theorem bochnerKernelSpace_closed (L : H →L[ℝ] G) (μ : Measure Ω) :
    IsClosed (bochnerKernelSpace L μ : Set (Lp H 2 μ)) := (L.compLpL 2 μ).isClosed_ker

omit [CompleteSpace H] in
theorem mem_bochnerKernelSpace_iff (L : H →L[ℝ] G) (μ : Measure Ω) (u : Lp H 2 μ) :
    u ∈ bochnerKernelSpace L μ ↔ ∀ᵐ x ∂μ, L (u x) = 0 := by
  change L.compLpL 2 μ u = 0 ↔ _
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have he := L.coeFn_compLpL u
  constructor
  · intro hz
    exact he.symm.trans hz
  · intro hz
    exact he.trans hz

omit [CompleteSpace H] in
theorem timeCellReconstruction_mem_bochnerKernel (g : TimeGrid) (L : H →L[ℝ] G)
    (u : Fin g.steps → H) (hu : ∀ i, L (u i) = 0) :
    timeCellReconstruction g u ∈ bochnerKernelSpace L (volume.restrict (Ioc 0 g.period)) := by
  apply (mem_bochnerKernelSpace_iff _ _ _).mpr
  filter_upwards [timeCellReconstruction_ae g u] with t ht
  rw [ht,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : t ∈ g.physicalTimeCell i
  · rw [indicator_of_mem hi,hu i]
  · rw [indicator_of_notMem hi,map_zero]

theorem exists_bochnerKernel_weak_subsequence (L : H →L[ℝ] G) (μ : Measure Ω)
    [TopologicalSpace.SeparableSpace (Lp H 2 μ)] (u : ℕ → Lp H 2 μ)
    (hu : ∀ n, ∀ᵐ x ∂μ, L (u n x) = 0) {C : ℝ} (hb : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : Lp H 2 μ, (∀ᵐ x ∂μ, L (v x) = 0) ∧ ‖v‖ ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ z : Lp H 2 μ,
        Tendsto (fun n => inner ℝ (u (φ n)) z) atTop (𝓝 (inner ℝ v z)) := by
  obtain ⟨v,hv,hvn,φ,hφ,ht⟩ := exists_hilbert_weak_subsequence_in_subspace
    (bochnerKernelSpace L μ) (bochnerKernelSpace_closed L μ) u
    (fun n => (mem_bochnerKernelSpace_iff L μ (u n)).mpr (hu n)) hb
  exact ⟨v,(mem_bochnerKernelSpace_iff L μ v).mp hv,hvn,φ,hφ,ht⟩

theorem bochnerKernel_of_weak_tendsto [CompleteSpace G] (L : H →L[ℝ] G) (μ : Measure Ω)
    (u : ℕ → Lp H 2 μ) (v : Lp H 2 μ)
    (hu : ∀ n, u n ∈ bochnerKernelSpace L μ)
    (ht : ∀ z : Lp H 2 μ, Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z))) :
    v ∈ bochnerKernelSpace L μ := by
  change L.compLpL 2 μ v = 0
  apply ext_inner_right ℝ
  intro z
  have hh := hilbert_weak_tendsto_map ht (L.compLpL 2 μ) z
  have hz : (fun n => inner ℝ (L.compLpL 2 μ (u n)) z) = fun _ => (0:ℝ) := by
    funext n
    have hn : L.compLpL 2 μ (u n) = 0 := hu n
    rw [hn,inner_zero_left]
  rw [hz] at hh
  simpa only [inner_zero_left] using tendsto_nhds_unique hh tendsto_const_nhds

end Carleman
