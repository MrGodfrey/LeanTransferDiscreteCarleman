module

public import Carleman.Control.TimeCellReconstruction
public import Carleman.Spatial.HilbertWeakSubsequence
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Actual reconstructed controls in a common Bochner space, with weak subsequences and the original cost. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace Carleman
variable {H U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

def reconstructedControl (T : ℝ) (g : TimeGrid) (hT : g.period = T) (K : U →L[ℝ] H)
    (u : Fin g.steps → U) : Lp H 2 (volume.restrict (Ioc 0 T)) :=
  hT ▸ timeCellReconstruction g (fun i => K (u i))

theorem reconstructedControl_norm (T : ℝ) (g : TimeGrid) (hT : g.period = T)
    (K : U →L[ℝ] H) (hK : ∀ v, ‖K v‖ = ‖v‖) (u : Fin g.steps → U) :
    ‖reconstructedControl T g hT K u‖ = Physical.controlNorm g.dt u := by
  subst T
  change ‖timeCellReconstruction g (fun i => K (u i))‖ = _
  rw [timeCellReconstruction_norm]
  simp only [Physical.controlNorm,hK]

omit [CompleteSpace H] in
theorem reconstructedControl_on_cell (T : ℝ) (g : TimeGrid) (hT : g.period = T)
    (K : U →L[ℝ] H) (u : Fin g.steps → U) (i : Fin g.steps) :
    ∀ᵐ t ∂volume.restrict (g.physicalTimeCell i), reconstructedControl T g hT K u t = K (u i) := by
  subst T
  exact timeCellReconstruction_on_cell g (fun j => K (u j)) i

theorem reconstructed_controls_weak_subsequence [TopologicalSpace.SeparableSpace H]
    {V : ℕ → Type*} [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ j, (g j).period = T)
    (K : ∀ j, V j →L[ℝ] H) (hK : ∀ j v, ‖K j v‖ = ‖v‖)
    (u : ∀ j, Fin (g j).steps → V j) {C : ℝ}
    (hb : ∀ j, Physical.controlNorm (g j).dt (u j) ≤ C) :
    ∃ v : Lp H 2 (volume.restrict (Ioc 0 T)), ‖v‖ ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ z : Lp H 2 (volume.restrict (Ioc 0 T)),
          Tendsto (fun n => inner ℝ
            (reconstructedControl T (g (φ n)) (hT (φ n)) (K (φ n)) (u (φ n))) z)
            atTop (𝓝 (inner ℝ v z)) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  apply exists_hilbert_weak_subsequence (fun j => reconstructedControl T (g j) (hT j) (K j) (u j))
  intro j
  rw [reconstructedControl_norm T (g j) (hT j) (K j) (hK j)]
  exact hb j

end Carleman
