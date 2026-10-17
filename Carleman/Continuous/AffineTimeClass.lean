module

public import Carleman.Periodic.AffineReconstruction
public import Carleman.Continuous.BochnerNorm

/-! The constructed affine path and its actual Bochner L² class. The order-dt
bound compares the original half-open extension and signed discrete derivative. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def affinePath (u : g.Sequence H) : g.TracePath (H := H) :=
  ⟨(Icc 0 g.period).domRestrict (g.affineReconstruction u),
    continuousOn_iff_continuous_domRestrict.mp (g.affineReconstruction_continuousOn u)⟩

def affineLp (u : g.Sequence H) : Lp H 2 g.timeMeasure := g.pathL2 (g.affinePath u)

theorem affineLp_ae (u : g.Sequence H) :
    g.affineLp u =ᵐ[g.timeMeasure] g.affineReconstruction u := by
  filter_upwards [g.pathL2_ae (g.affinePath u), ae_restrict_mem measurableSet_Ioo] with t ht hm
  exact ht.trans (g.clampPath_on (g.affinePath u) t ⟨hm.1.le,hm.2.le⟩)

variable [CompleteSpace H]

theorem affineLp_defect_le (s : Orientation) (u : g.Sequence H) :
    ‖g.affineLp u - s.extensionLp g u‖ ≤ g.dt * g.l2Norm (s.difference g u) := by
  rw [← s.extensionLp_norm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (g.affineLp u) (s.extensionLp g u), g.affineLp_ae u,
    s.extensionLp_ae g u, s.extensionLp_ae g (s.difference g u), s.affine_defect_ae g u]
    with t hsub ha hu hd ht
  simp only [Pi.sub_apply] at hsub
  rwa [hsub, ha, hu, hd]

/-- The function-level statement uses the real Bochner norm, with its finiteness proved. -/
theorem affine_bochner_defect_le (s : Orientation) (u : g.Sequence H) :
    MemLp (fun t => g.affineReconstruction u t - s.extension g u t) 2 g.timeMeasure ∧
      bochnerL2Norm g.timeMeasure (fun t => g.affineReconstruction u t - s.extension g u t) ≤
        g.dt * g.l2Norm (s.difference g u) := by
  have hm := (g.memLp_of_continuousOn (g.affineReconstruction_continuousOn u)).sub (s.memLp_extension g u)
  change MemLp (fun t => g.affineReconstruction u t - s.extension g u t) 2 g.timeMeasure at hm
  refine ⟨hm, ?_⟩
  rw [bochnerL2Norm_eq _ hm]
  have he : hm.toLp (fun t => g.affineReconstruction u t - s.extension g u t) =
      g.affineLp u - s.extensionLp g u := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp, Lp.coeFn_sub (g.affineLp u) (s.extensionLp g u),
      g.affineLp_ae u, s.extensionLp_ae g u] with t ht hs ha hu
    simp only [Pi.sub_apply] at hs
    rw [ht, hs, ha, hu]
  rw [he]
  exact g.affineLp_defect_le s u
end Carleman.TimeGrid
