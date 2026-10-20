module

public import Carleman.Control.PivotTimeTrace
public import Carleman.Control.MassRegularizedPaths

/-! The actual mass-derivative graph has an H-continuous representative, by uniform convergence of genuine regularized paths. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace V] in
theorem HasWeakTimeDerivative.sub_memLp {g : TimeGrid} {u v du dv : ℝ → V}
    (hw : HasWeakTimeDerivative g u du) (hv : HasWeakTimeDerivative g v dv)
    (hu : MemLp u 2 g.timeMeasure) (hvm : MemLp v 2 g.timeMeasure)
    (hd : MemLp du 2 g.timeMeasure) (hdv : MemLp dv 2 g.timeMeasure) :
    HasWeakTimeDerivative g (fun t => u t-v t) (fun t => du t-dv t) := by
  intro φ hs hc hsup
  have hφ := g.memLp_of_continuousOn hs.continuous.continuousOn
  have hdφ := g.memLp_of_continuousOn (hs.continuous_deriv (by simp)).continuousOn
  have hiu : Integrable (fun t => deriv φ t • u t) g.timeMeasure := memLp_one_iff_integrable.mp (hdφ.smul hu)
  have hiv : Integrable (fun t => deriv φ t • v t) g.timeMeasure := memLp_one_iff_integrable.mp (hdφ.smul hvm)
  have hid : Integrable (fun t => φ t • du t) g.timeMeasure := memLp_one_iff_integrable.mp (hφ.smul hd)
  have hidv : Integrable (fun t => φ t • dv t) g.timeMeasure := memLp_one_iff_integrable.mp (hφ.smul hdv)
  simp_rw [smul_sub]
  rw [integral_sub hiu hiv,integral_sub hid hidv,hw φ hs hc hsup,hv φ hs hc hsup]
  abel

theorem pivot_path_limit {g : TimeGrid} (E : V →L[ℝ] H)
    (u du : ℕ → ℝ → V) (hu : ∀ n, ContinuousOn (u n) (Icc 0 g.period))
    (hd : ∀ n, MemLp (du n) 2 g.timeMeasure)
    (hw : ∀ n, HasWeakTimeDerivative g (u n) (du n))
    (Y D : Lp V 2 g.timeMeasure)
    (hY : Tendsto (fun n => (g.memLp_of_continuousOn (hu n)).toLp (u n)) atTop (𝓝 Y))
    (hD : Tendsto (fun n => ((hd n).continuousLinearMap_comp (E.adjoint.comp E)).toLp
      (fun t => E.adjoint (E (du n t)))) atTop (𝓝 D)) :
    ∃ p : g.TracePath (H := H), g.pathL2 p=E.compLpL 2 g.timeMeasure Y := by
  let U n := (g.memLp_of_continuousOn (hu n)).toLp (u n)
  let Z n := ((hd n).continuousLinearMap_comp (E.adjoint.comp E)).toLp (fun t => E.adjoint (E (du n t)))
  let p (n : ℕ) : g.TracePath (H := H) := ⟨fun t => E (u n t),
    E.continuous.comp (continuousOn_iff_continuous_domRestrict.mp (hu n))⟩
  have hpnorm (n m : ℕ) :
      ‖p n-p m‖ ≤ Real.sqrt (‖E.compLpL 2 g.timeMeasure (U n-U m)‖^2/g.period+
        2*‖U n-U m‖*‖Z n-Z m‖) := by
    apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr
    intro t
    have huc : ContinuousOn (fun t => u n t-u m t) (Icc 0 g.period) := (hu n).sub (hu m)
    have hdc : MemLp (fun t => du n t-du m t) 2 g.timeMeasure := (hd n).sub (hd m)
    have hwc := (hw n).sub_memLp (hw m) (g.memLp_of_continuousOn (hu n))
      (g.memLp_of_continuousOn (hu m)) (hd n) (hd m)
    have hb := hwc.pivot_trace_bound huc hdc E t.property
    dsimp only at hb
    have heU : (g.memLp_of_continuousOn huc).toLp (fun t => u n t-u m t)=U n-U m := by
      apply Lp.ext
      filter_upwards [(g.memLp_of_continuousOn huc).coeFn_toLp,
        (g.memLp_of_continuousOn (hu n)).coeFn_toLp,
        (g.memLp_of_continuousOn (hu m)).coeFn_toLp,Lp.coeFn_sub (U n) (U m)] with x he hn hm hs
      exact he.trans (by rw [hs]; change u n x-u m x=U n x-U m x; rw [hn,hm])
    have heE : ((g.memLp_of_continuousOn huc).continuousLinearMap_comp E).toLp
        (fun t => E (u n t-u m t))=E.compLpL 2 g.timeMeasure (U n-U m) := by
      rw [← heU]
      apply Lp.ext
      filter_upwards [((g.memLp_of_continuousOn huc).continuousLinearMap_comp E).coeFn_toLp,
        E.coeFn_compLpL ((g.memLp_of_continuousOn huc).toLp (fun t => u n t-u m t)),
        (g.memLp_of_continuousOn huc).coeFn_toLp] with x he hf hv
      rw [he,hf,hv]
    have heZ : ((hdc.continuousLinearMap_comp E).continuousLinearMap_comp E.adjoint).toLp
        (fun t => E.adjoint (E (du n t-du m t)))=Z n-Z m := by
      apply Lp.ext
      filter_upwards [((hdc.continuousLinearMap_comp E).continuousLinearMap_comp E.adjoint).coeFn_toLp,
        ((hd n).continuousLinearMap_comp (E.adjoint.comp E)).coeFn_toLp,
        ((hd m).continuousLinearMap_comp (E.adjoint.comp E)).coeFn_toLp,Lp.coeFn_sub (Z n) (Z m)] with x he hn hm hs
      rw [he,hs]
      change E.adjoint (E (du n x-du m x))=Z n x-Z m x
      change Z n x=E.adjoint (E (du n x)) at hn
      change Z m x=E.adjoint (E (du m x)) at hm
      rw [hn,hm,map_sub,map_sub]
    rw [heU,heE,heZ] at hb
    change ‖E (u n t)-E (u m t)‖ ≤ _
    rw [← map_sub]
    exact (Real.le_sqrt (norm_nonneg _) (by have hT := g.period_pos; positivity)).mpr hb
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_snd
  have hUd : Tendsto (fun nm : ℕ × ℕ => U nm.1-U nm.2) atTop (𝓝 0) := by
    simpa only [U,Function.comp_def,sub_self] using (hY.comp hfst).sub (hY.comp hsnd)
  have hZd : Tendsto (fun nm : ℕ × ℕ => Z nm.1-Z nm.2) atTop (𝓝 0) := by
    simpa only [Z,Function.comp_def,sub_self] using (hD.comp hfst).sub (hD.comp hsnd)
  have hEd := ((E.compLpL 2 g.timeMeasure).continuous.tendsto 0).comp hUd
  have hbound : Tendsto (fun nm : ℕ × ℕ => Real.sqrt
      (‖E.compLpL 2 g.timeMeasure (U nm.1-U nm.2)‖^2/g.period+
        2*‖U nm.1-U nm.2‖*‖Z nm.1-Z nm.2‖)) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((hEd.norm.pow 2 |>.div_const g.period).add ((hUd.norm.const_mul 2).mul hZd.norm))
    simpa only [Function.comp_def,map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_div,mul_zero,zero_mul,add_zero,Real.sqrt_zero] using h
  have hpc : CauchySeq p := by
    apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun nm => ?_) hbound
    simpa only [dist_eq_norm] using hpnorm nm.1 nm.2
  obtain ⟨q,hq⟩ := cauchySeq_tendsto_of_complete hpc
  have hpclass n : g.pathL2 (p n)=E.compLpL 2 g.timeMeasure (U n) := by
    apply Lp.ext
    filter_upwards [g.pathL2_ae (p n),E.coeFn_compLpL (U n),
      (g.memLp_of_continuousOn (hu n)).coeFn_toLp,ae_restrict_mem measurableSet_Ioo] with t hp he hu ht
    rw [hp,g.clampPath_on (p n) t ⟨ht.1.le,ht.2.le⟩,he,hu]
    rfl
  refine ⟨q,?_⟩
  have hqL := (g.pathL2.continuous.tendsto q).comp hq
  have hYL := ((E.compLpL 2 g.timeMeasure).continuous.tendsto Y).comp hY
  change Tendsto (fun n => g.pathL2 (p n)) atTop (𝓝 (g.pathL2 q)) at hqL
  simp_rw [hpclass] at hqL
  exact tendsto_nhds_unique hqL hYL

theorem exists_pivot_time_representative {g : TimeGrid} {μ : Measure ℝ}
    (hμ : g.timeMeasure=μ) (E : V →L[ℝ] H) (hE : Function.Injective E)
    (Y D : Lp V 2 μ)
    (hw : HasWeakTimeDerivative g ((E.adjoint.comp E).compLpL 2 μ Y) D) :
    ∃ q : ℝ → H, ContinuousOn q (Icc 0 g.period) ∧ q =ᵐ[μ] (fun t => E (Y t)) := by
  subst μ
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
  have hY' : Tendsto (fun n => (g.memLp_of_continuousOn (huc n)).toLp (u n)) atTop (𝓝 Y) := hucon
  have hD' : Tendsto (fun n => ((hd n).continuousLinearMap_comp (E.adjoint.comp E)).toLp
      (fun t => E.adjoint (E (du n t)))) atTop (𝓝 D) := hdcon
  obtain ⟨p,hp⟩ := pivot_path_limit E u du huc hd huweak Y D hY' hD'
  refine ⟨g.clampPath p,(g.clampPath p).continuous.continuousOn,?_⟩
  exact (g.pathL2_ae p).symm.trans (by rw [hp]; exact E.coeFn_compLpL Y)

end Carleman
