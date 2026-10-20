module

public import Carleman.Control.TimeCutoffPairing

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman

theorem time_cutoff_norm_sq_of_ae {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T t : ℝ} (ht : t ∈ Icc 0 T) (Z : Lp H 2 (volume.restrict (Ioc 0 T)))
    (q : ℝ → H) (hq : q =ᵐ[volume.restrict (Ioc 0 T)] Z) :
    ‖(BoundedMultiplier.cutoff (Ioc 0 t) measurableSet_Ioc).map Z‖^2=
      ∫ s in 0..t, ‖q s‖^2 := by
  rw [← real_inner_self_eq_norm_sq,← cutoff_inner_cutoff,cutoff_inner_integral,
    intervalIntegral.integral_of_le ht.1]
  have hμ : (volume.restrict (Ioc 0 T)).restrict (Ioc 0 t)=volume.restrict (Ioc 0 t) := by
    rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (Ioc_subset_Ioc le_rfl ht.2)]
  have ha : q =ᵐ[volume.restrict (Ioc 0 t)] Z := by
    rw [← hμ]
    exact hq.filter_mono ae_restrict_le
  rw [hμ]
  apply integral_congr_ae
  filter_upwards [ha] with s hs
  rw [← hs,real_inner_self_eq_norm_sq]


end Carleman
