module

public import Carleman.Control.PivotIntervalEnergy
public import Carleman.Control.PivotPathConvergence

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_pivot_time_energy_representative {g : TimeGrid}
    (E : V →L[ℝ] H) (hE : Function.Injective E)
    (Y D : Lp V 2 g.timeMeasure)
    (hw : HasWeakTimeDerivative g ((E.adjoint.comp E).compLpL 2 g.timeMeasure Y) D) :
    ∃ q : ℝ → H, ContinuousOn q (Icc 0 g.period) ∧
      q =ᵐ[g.timeMeasure] (fun t => E (Y t)) ∧
      ∀ t ∈ Icc 0 g.period,
        ‖q t‖^2-‖q 0‖^2=2*(∫ s in 0..t, inner ℝ (Y s) (D s)) := by
  let M := E.adjoint.comp E
  have hM (v : V) : 0 ≤ inner ℝ (M v) v := by
    change 0 ≤ inner ℝ (E.adjoint (E v)) v
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact real_inner_self_nonneg
  let ε (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hε n : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨u,du,hum,hd,huc,huweak,huae,hdae,hucon,hdcon⟩ :=
    mass_regularized_time_paths M hM (adjoint_mass_denseRange E hE) rfl Y D hw ε hε hlim
  let U n := (g.memLp_of_continuousOn (huc n)).toLp (u n)
  let Z n := ((hd n).continuousLinearMap_comp M).toLp (fun t => M (du n t))
  have hY' : Tendsto U atTop (𝓝 Y) := hucon
  have hD' : Tendsto Z atTop (𝓝 D) := hdcon
  obtain ⟨p,hp,hpc⟩ := pivot_path_limit_strong E u du huc hd huweak Y D hY' hD'
  refine ⟨g.clampPath p,(g.clampPath p).continuous.continuousOn,?_,?_⟩
  · exact (g.pathL2_ae p).symm.trans (by rw [hp]; exact E.coeFn_compLpL Y)
  · intro t ht
    have hpt (s : ℝ) (hs : s ∈ Icc 0 g.period) :
        Tendsto (fun n => E (u n s)) atTop (𝓝 (g.clampPath p s)) := by
      have hh := ((ContinuousMap.evalCLM ℝ (⟨s,hs⟩ : Icc 0 g.period)).continuous.tendsto p).comp hpc
      rw [g.clampPath_on p s hs]
      exact hh
    let R := Physical.restrictRegionCLM (ν := g.timeMeasure) (E := V) (Ioc 0 t)
    have hi := (((R.continuous.tendsto Y).comp hY').inner (𝕜 := ℝ) ((R.continuous.tendsto D).comp hD')).const_mul (2:ℝ)
    have he n : 2*inner ℝ (R (U n)) (R (Z n))=‖E (u n t)‖^2-‖E (u n 0)‖^2 := by
      rw [time_restrict_inner_integral (U n) (Z n) ht]
      have hμ : g.timeMeasure.restrict (Ioc 0 t)=volume.restrict (Ioc 0 t) := by
        change (volume.restrict (Ioo 0 g.period)).restrict (Ioc 0 t)=_
        rw [restrict_Ioo_eq_restrict_Ioc,Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.mpr (Ioc_subset_Ioc le_rfl ht.2)]
      have heU : U n =ᵐ[g.timeMeasure.restrict (Ioc 0 t)] u n :=
        ((g.memLp_of_continuousOn (huc n)).coeFn_toLp).filter_mono ae_restrict_le
      have heZ : Z n =ᵐ[g.timeMeasure.restrict (Ioc 0 t)] (fun s => M (du n s)) :=
        (((hd n).continuousLinearMap_comp M).coeFn_toLp).filter_mono ae_restrict_le
      have hpair : (fun s => inner ℝ (U n s) (Z n s)) =ᵐ[volume.restrict (Ioc 0 t)]
          (fun s => inner ℝ (u n s) (M (du n s))) := by
        rw [← hμ]
        filter_upwards [heU,heZ] with s hs hz
        rw [hs,hz]
      rw [intervalIntegral.integral_of_le ht.1,integral_congr_ae hpair,
        ← intervalIntegral.integral_of_le ht.1]
      exact (huweak n).pivot_energy_identity_to (huc n) (hd n) E ht
    have hleft := (hpt t ht).norm.pow 2 |>.sub ((hpt 0 ⟨le_rfl,g.period_pos.le⟩).norm.pow 2)
    have hright : Tendsto (fun n => ‖E (u n t)‖^2-‖E (u n 0)‖^2) atTop
        (𝓝 (2*inner ℝ (R Y) (R D))) := by simpa only [Function.comp_def,he] using hi
    exact (tendsto_nhds_unique hleft hright).trans (by rw [time_restrict_inner_integral Y D ht])

theorem pivot_time_energy_identity {g : TimeGrid} {μ : Measure ℝ}
    (hμ : g.timeMeasure=μ) (E : V →L[ℝ] H) (hE : Function.Injective E)
    (Y D : Lp V 2 μ)
    (hw : HasWeakTimeDerivative g ((E.adjoint.comp E).compLpL 2 μ Y) D)
    (q : ℝ → H) (hq : ContinuousOn q (Icc 0 g.period))
    (hae : q =ᵐ[μ] (fun t => E (Y t))) :
    ∀ t ∈ Icc 0 g.period,
      ‖q t‖^2-‖q 0‖^2=2*(∫ s in 0..t, inner ℝ (Y s) (D s)) := by
  subst μ
  obtain ⟨p,hp,hpae,he⟩ := exists_pivot_time_energy_representative E hE Y D hw
  have heq := g.continuous_representative_unique hq hp (hae.trans hpae.symm)
  intro t ht
  rw [heq ht,heq ⟨le_rfl,g.period_pos.le⟩]
  exact he t ht


end Carleman
