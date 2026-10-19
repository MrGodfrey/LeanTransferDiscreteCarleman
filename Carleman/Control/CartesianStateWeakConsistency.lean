module

public import Carleman.Control.TimeReconstructionEstimates
public import Carleman.Control.HilbertWeakPerturbation
public import Carleman.Spatial.FixedBoxKuhnConsistency

/-! The original E_h and R_h time reconstructions share weak limits under the actual gradient budget. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem cartesianBoxCell_kuhn_time_consistency : ∃ C > (0:ℝ),
    ∀ (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (h : ℝ) (_hh : 0 ≤ h) (_hstep : ∀ j, δ j ≤ h)
      (T : ℝ) (g : TimeGrid) (hT : g.period=T) (u : Fin g.steps → CartesianPhysicalState δ hδ N),
      ‖fixedTimeCellReconstruction T g hT (fun i => cartesianBoxCellIsometry lo hi δ hδ N hbox (u i))-
        fixedTimeCellReconstruction T g hT (fun i => WeakSobolevJet.value
          (cartesianBoxKuhnReconstructionJet lo hi δ hδ N hbox (u i)))‖ ≤
        C*h*‖fixedTimeCellReconstruction T g hT (fun i => WeakSobolevJet.field 1
          (cartesianBoxKuhnReconstructionJet lo hi δ hδ N hbox (u i)))‖ := by
  obtain ⟨C,hC,hbound⟩ := cartesianBoxCell_kuhn_L2_consistency (d := d)
  refine ⟨C,hC,?_⟩
  intro lo hi δ hδ N hbox h hh hstep T g hT u
  rw [← fixedTimeCellReconstruction_sub]
  exact fixedTimeCellReconstruction_norm_le T g hT _ _ (mul_nonneg hC.le hh)
    (fun i => hbound lo hi δ hδ N hbox h hh hstep (u i))

theorem cartesianBoxCell_kuhn_time_error_tendsto
    (lo hi : Fin d → ℝ) (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j)
    (N : ℕ → Fin d → ℕ) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (u : ∀ n, Fin (g n).steps → CartesianPhysicalState (δ n) (hδ n) (N n))
    {B : ℝ} (hb : ∀ n, ‖fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => WeakSobolevJet.field 1
        (cartesianBoxKuhnReconstructionJet lo hi (δ n) (hδ n) (N n) (hbox n) (u n i)))‖ ≤ B) :
    Tendsto (fun n =>
      ‖fixedTimeCellReconstruction T (g n) (hT n)
          (fun i => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (u n i))-
        fixedTimeCellReconstruction T (g n) (hT n) (fun i => WeakSobolevJet.value
          (cartesianBoxKuhnReconstructionJet lo hi (δ n) (hδ n) (N n) (hbox n) (u n i)))‖)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := cartesianBoxCell_kuhn_time_consistency (d := d)
  have hm : Tendsto (fun n => C*h n*B) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using ((tendsto_const_nhds (x := C)).mul hlim).mul_const B
  apply squeeze_zero (fun _ => norm_nonneg _) _ hm
  intro n
  exact (hbound lo hi (δ n) (hδ n) (N n) (hbox n) (h n) (hh n) (hstep n) T (g n) (hT n) (u n)).trans
    (mul_le_mul_of_nonneg_left (hb n) (mul_nonneg hC.le (hh n)))

theorem cartesianBoxCell_kuhn_same_weak_limit
    (lo hi : Fin d → ℝ) (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j)
    (N : ℕ → Fin d → ℕ) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (u : ∀ n, Fin (g n).steps → CartesianPhysicalState (δ n) (hδ n) (N n))
    {B : ℝ} (hb : ∀ n, ‖fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => WeakSobolevJet.field 1
        (cartesianBoxKuhnReconstructionJet lo hi (δ n) (hδ n) (N n) (hbox n) (u n i)))‖ ≤ B)
    (y : Lp (Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) 2 (volume.restrict (Ioc 0 T)))
    (hweak : ∀ w : Lp (Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) 2 (volume.restrict (Ioc 0 T)),
      Tendsto (fun n => inner ℝ
        (fixedTimeCellReconstruction T (g n) (hT n) (fun i => WeakSobolevJet.value
          (cartesianBoxKuhnReconstructionJet lo hi (δ n) (hδ n) (N n) (hbox n) (u n i)))) w)
        atTop (𝓝 (inner ℝ y w))) :
    ∀ w : Lp (Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) 2 (volume.restrict (Ioc 0 T)),
      Tendsto (fun n => inner ℝ
        (fixedTimeCellReconstruction T (g n) (hT n)
          (fun i => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (u n i))) w)
        atTop (𝓝 (inner ℝ y w)) := by
  exact hilbert_weak_of_norm_sub_tendsto_zero _ _ y
    (cartesianBoxCell_kuhn_time_error_tendsto lo hi δ hδ N hbox h hh hstep hlim T g hT u hb) hweak

end Carleman
