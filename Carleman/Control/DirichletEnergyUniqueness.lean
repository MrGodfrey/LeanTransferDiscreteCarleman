module

public import Carleman.Control.VolterraEnergyUniqueness
public import Carleman.Control.TimeCutoffEnergyNorm
public import Carleman.Control.DirichletLocalEnergy

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman

set_option backward.isDefEq.respectTransparency true in
theorem dirichlet_mass_energy_zero
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (g : TimeGrid) (hT : g.period=T)
    (hw : HasWeakTimeDerivative g ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y)
      (dirichletTimeLoad T hS b Y 0))
    (q : ℝ → Lp ℝ 2 (volume.restrict S)) (hc : ContinuousOn q (Icc 0 T))
    (hq : q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)))
    (hzero : q 0=0) : Y=0 ∧ ∀ t ∈ Icc 0 T, q t=0 := by
  let := dirichletEnergyState_complete hS
  have hTpos : 0 < T := hT ▸ g.period_pos
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 T) := by
    rw [TimeGrid.timeMeasure,hT,restrict_Ioo_eq_restrict_Ioc]
  have hE : Function.Injective (dirichletStateValue S) :=
    conformingEmbed_injective (dirichletSubspace S) hS (ae_restrict_mem hS.measurableSet)
  have he := pivot_time_energy_identity (V := DirichletEnergyState S) hμ
    (dirichletStateValue S) hE Y (dirichletTimeLoad T hS b Y 0) hw q (by rwa [hT]) hq
  let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y
  have hqv : q =ᵐ[volume.restrict (Ioc 0 T)] Yv := hq.trans ((dirichletStateValue S).coeFn_compLpL Y).symm
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) : ‖q t‖^2 ≤ (2*b.bound)*(∫ s in 0..t, ‖q s‖^2) := by
    let W := BoundedMultiplier.cutoff (ν := volume.restrict (Ioc 0 T)) (Ioc 0 t) measurableSet_Ioc
    have hh := he t (by rwa [hT])
    rw [hzero,norm_zero,zero_pow (by decide : 2≠0),sub_zero] at hh
    have hi : inner ℝ (dirichletTimeLoad T hS b Y 0) (W.map Y)=
        ∫ s in 0..t, inner ℝ (Y s) (dirichletTimeLoad T hS b Y 0 s) := by
      rw [cutoff_inner_integral,intervalIntegral.integral_of_le ht.1]
      have hm : (volume.restrict (Ioc 0 T)).restrict (Ioc 0 t)=volume.restrict (Ioc 0 t) := by
        rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (Ioc_subset_Ioc le_rfl ht.2)]
      rw [hm]
      exact integral_congr_ae (Eventually.of_forall fun _ => real_inner_comm _ _)
    have hb := dirichletTimeLoad_cutoff_upper_bound T hS b Y 0 (Ioc 0 t) measurableSet_Ioc
    dsimp only at hb
    rw [show W.map (0 : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)))=0
      from _root_.map_zero W.linearMap,norm_zero,zero_mul,zero_add] at hb
    rw [← hi] at hh
    have hn := time_cutoff_norm_sq_of_ae ht Yv q hqv
    change ‖W.map Yv‖^2=_ at hn
    rw [← hn]
    nlinarith [sq_nonneg (‖W.map ((dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y)‖)]
  have hnorm := continuous_volterra_nonneg_eq_zero hTpos (by positivity [b.bound_nonneg])
    (hc.norm.pow 2) (fun _ _ => sq_nonneg _) hbound
  have hqzero : ∀ t ∈ Icc 0 T, q t=0 := fun t ht => norm_eq_zero.mp (sq_eq_zero_iff.mp (hnorm t ht))
  refine ⟨?_,hqzero⟩
  apply Lp.ext
  filter_upwards [hq,ae_restrict_mem measurableSet_Ioc,
    Lp.coeFn_zero (E := DirichletEnergyState S) (p := 2) (μ := volume.restrict (Ioc 0 T))]
      with t ht hm hz
  rw [hz]
  change Y t=0
  apply hE
  rw [map_zero,← ht,hqzero t ⟨hm.1.le,hm.2⟩]

set_option backward.isDefEq.respectTransparency true in
theorem dirichletTimeLoad_sub
    {d : ℕ} {S : Set (SpatialCoordinates d)} (T : ℝ) (hS : IsOpen S)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y Z : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U W : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))) :
    dirichletTimeLoad T hS b (Y-Z) (U-W)=dirichletTimeLoad T hS b Y U-dirichletTimeLoad T hS b Z W := by
  let := dirichletEnergyState_complete hS
  dsimp only [dirichletTimeLoad]
  simp only [← b.continuousLinearMap_apply,_root_.map_sub]
  abel

set_option backward.isDefEq.respectTransparency true in
theorem dirichlet_mass_energy_unique
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (Y Z : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)))
    (g : TimeGrid) (hT : g.period=T)
    (hY : HasWeakTimeDerivative g ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Y)
      (dirichletTimeLoad T hS b Y U))
    (hZ : HasWeakTimeDerivative g ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Z)
      (dirichletTimeLoad T hS b Z U))
    (q r : ℝ → Lp ℝ 2 (volume.restrict S))
    (hq : ContinuousOn q (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hqa : q =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Y t)))
    (hra : r =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Z t)))
    (hinit : q 0=r 0) : Y=Z ∧ ∀ t ∈ Icc 0 T, q t=r t := by
  let := dirichletEnergyState_complete hS
  have hμ : g.timeMeasure=volume.restrict (Ioc 0 T) := by
    rw [TimeGrid.timeMeasure,hT,restrict_Ioo_eq_restrict_Ioc]
  let M := (dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T))
  let DY := dirichletTimeLoad T hS b Y U
  let DZ := dirichletTimeLoad T hS b Z U
  have hsub := hY.sub_memLp hZ (by rw [hμ]; exact Lp.memLp (M Y))
    (by rw [hμ]; exact Lp.memLp (M Z)) (by rw [hμ]; exact Lp.memLp DY)
    (by rw [hμ]; exact Lp.memLp DZ)
  have hv : (fun t => M Y t-M Z t) =ᵐ[g.timeMeasure] (M (Y-Z)) := by
    rw [hμ,_root_.map_sub]
    exact (Lp.coeFn_sub (M Y) (M Z)).symm
  have hd : (fun t => DY t-DZ t) =ᵐ[g.timeMeasure] (dirichletTimeLoad T hS b (Y-Z) 0) := by
    rw [hμ,show dirichletTimeLoad T hS b (Y-Z) 0=DY-DZ from by
      simpa only [sub_self] using dirichletTimeLoad_sub T hS b Y Z U U]
    exact (Lp.coeFn_sub DY DZ).symm
  have hqr : (fun t => q t-r t) =ᵐ[volume.restrict (Ioc 0 T)]
      (fun t => dirichletStateValue S ((Y-Z) t)) := by
    filter_upwards [hqa,hra,Lp.coeFn_sub Y Z] with t ht hs he
    rw [ht,hs,he]
    exact (_root_.map_sub (dirichletStateValue S) (Y t) (Z t)).symm
  obtain ⟨hz,hqt⟩ := dirichlet_mass_energy_zero hS b (Y-Z) g hT
    ((hsub.congr_value hv).congr_derivative hd) (fun t => q t-r t) (hq.sub hr) hqr
    (sub_eq_zero.mpr hinit)
  exact ⟨sub_eq_zero.mp hz,fun t ht => sub_eq_zero.mp (hqt t ht)⟩

set_option backward.isDefEq.respectTransparency true in
theorem FiniteDirichletControlIdentity.identifies_energy_solution
    {d : ℕ} {S : Set (SpatialCoordinates d)} {T : ℝ}
    (hS : IsOpen S) [IsFiniteMeasure (volume.restrict S)]
    {b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S))}
    {y0 : Lp ℝ 2 (volume.restrict S)}
    {Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))}
    {U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))}
    (hid : FiniteDirichletControlIdentity T S b y0 Y U)
    (Z : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (g : TimeGrid) (hT : g.period=T)
    (hZ : HasWeakTimeDerivative g ((dirichletTimeMass S hS).compLpL 2 (volume.restrict (Ioc 0 T)) Z)
      (dirichletTimeLoad T hS b Z U))
    (r : ℝ → Lp ℝ 2 (volume.restrict S)) (hr : ContinuousOn r (Icc 0 T))
    (hra : r =ᵐ[volume.restrict (Ioc 0 T)] (fun t => dirichletStateValue S (Z t)))
    (hinit : r 0=y0) : Y=Z ∧ r T=0 := by
  have hTpos : 0 < T := hT ▸ g.period_pos
  obtain ⟨q,hq,hqa,hq0,hqT⟩ := hid.continuous_H_trace hTpos hS
  obtain ⟨hYZ,hqr⟩ := dirichlet_mass_energy_unique hS b Y Z U g hT
    (hid.mass_weak_time_derivative hS g hT) hZ q r hq hr hqa hra (hq0.trans hinit.symm)
  exact ⟨hYZ,(hqr T ⟨hTpos.le,le_rfl⟩).symm.trans hqT⟩


end Carleman
