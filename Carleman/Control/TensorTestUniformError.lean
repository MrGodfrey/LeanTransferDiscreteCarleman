module

public import Carleman.Control.SpatialTestUniformError
public import Carleman.Control.BochnerProductL2
public import Carleman.Control.FixedTimeCellStrongConvergence

/-! Uniform errors for finite original time samples and actual Bochner product representatives. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem timeCell_ae_covered (T : ℝ) (g : TimeGrid) (hT : g.period=T) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 T), ∃ i : Fin g.steps, t ∈ g.physicalTimeCell i := by
  have hz := (measureReal_eq_zero_iff (μ := volume.restrict (Ioc 0 T))).mp
    (fixedTimeCell_uncovered_volume T (hT ▸ g.period_pos.le) g hT)
  have hm : ∀ᵐ t ∂volume.restrict (Ioc 0 T), t ∈ ⋃ i, g.physicalTimeCell i := by
    rw [ae_iff]
    exact hz
  filter_upwards [hm] with t ht
  exact mem_iUnion.mp ht

theorem finite_time_tensor_uniform_error {Ω L : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [SFinite ν] [Fintype L]
    (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (η : L → ℝ → ℝ) (ψ v : L → Ω → ℝ) (A B ε : L → ℝ) (C : L → ℝ≥0)
    (hA : ∀ l, 0 ≤ A l) (ha : ∀ l t, t ∈ Icc 0 T → |η l t| ≤ A l)
    (hη : ∀ l, LipschitzOnWith (C l) (η l) (Icc 0 T))
    (hb : ∀ l, ∀ᵐ x ∂ν, |ψ l x| ≤ B l)
    (hv : ∀ l, ∀ᵐ x ∂ν, |v l x-ψ l x| ≤ ε l) :
    ∀ᵐ z ∂(volume.restrict (Ioc 0 T)).prod ν,
      |finiteCellFunction g.physicalTimeCell (fun i => ∑ l, η l (g.nodeTime i)*v l z.2) z.1-
        ∑ l, η l z.1*ψ l z.2| ≤ ∑ l, (A l*ε l+(C l:ℝ)*g.dt*B l) := by
  have haev := Filter.eventually_all.mpr hv
  have haeb := Filter.eventually_all.mpr hb
  filter_upwards [quasiMeasurePreserving_fst.ae (timeCell_ae_covered T g hT),
    quasiMeasurePreserving_snd.ae haev,quasiMeasurePreserving_snd.ae haeb] with z htz hvz hbz
  obtain ⟨i,hi⟩ := htz
  have hti : g.nodeTime i ∈ Icc 0 T := by
    refine ⟨g.nodeTime_nonneg i,?_⟩
    rw [← hT]
    dsimp [TimeGrid.nodeTime,TimeGrid.period]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast i.isLt.le) g.dt_pos.le
  have htz' : z.1 ∈ Icc 0 T := by
    have hh := g.physicalTimeCell_subset i hi
    exact ⟨hh.1.le,hT ▸ hh.2⟩
  have hd : dist (g.nodeTime i) z.1 ≤ g.dt := by
    rw [dist_comm,Real.dist_eq,abs_of_pos (sub_pos.mpr hi.1)]
    linarith [hi.2]
  rw [finiteCellFunction_on_cell _ g.physicalTimeCell_disjoint _ i hi,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  have he : η l (g.nodeTime i)*v l z.2-η l z.1*ψ l z.2=
      η l (g.nodeTime i)*(v l z.2-ψ l z.2)+(η l (g.nodeTime i)-η l z.1)*ψ l z.2 := by ring
  rw [he]
  have ht : |η l (g.nodeTime i)-η l z.1| ≤ (C l:ℝ)*g.dt :=
    ((hη l).dist_le_mul _ hti _ htz').trans (mul_le_mul_of_nonneg_left hd (C l).coe_nonneg)
  exact (abs_add_le _ _).trans (by
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul (ha l _ hti) (hvz l) (abs_nonneg _) (hA l))
      (mul_le_mul ht (hbz l) (abs_nonneg _) (mul_nonneg (C l).coe_nonneg g.dt_pos.le)))

theorem finite_tensor_test_bounds {S : Set (SpatialCoordinates d)} {L : Type*} [Fintype L]
    (T : ℝ) (η f : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    ∃ A B C D : L → ℝ≥0,
      (∀ l t, t ∈ Icc 0 T → |η l t| ≤ A l) ∧
      (∀ l, LipschitzOnWith (C l) (η l) (Icc 0 T)) ∧
      (∀ l x, |(ψ l).value x| ≤ B l) ∧ (∀ l, LipschitzWith (D l) (ψ l).value) := by
  have ha l : ∃ A : ℝ≥0, ∀ t ∈ Icc 0 T, |η l t| ≤ A := by
    obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn (hη l)
    exact ⟨⟨max 0 A,le_max_left _ _⟩,fun t ht => (hA t ht).trans (le_max_right _ _)⟩
  have hb l : ∃ B : ℝ≥0, ∀ x, |(ψ l).value x| ≤ B := by
    obtain ⟨B,hB⟩ := (ψ l).compact.exists_bound_of_continuous (ψ l).smooth.continuous
    exact ⟨⟨max 0 B,le_max_left _ _⟩,fun x => (hB x).trans (le_max_right _ _)⟩
  choose A hA using ha
  choose B hB using hb
  choose C hC using fun l => time_test_lipschitz T (η l) (f l) (hd l) (hf l)
  choose D hD using fun l => ContDiff.lipschitzWith_of_hasCompactSupport
    (ψ l).compact (ψ l).smooth (by simp)
  exact ⟨A,B,C,D,hA,hC,hB,hD⟩

theorem bochner_finite_time_tensor_ae {Ω L : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [SFinite ν] [Fintype L]
    (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (η : L → ℝ → ℝ) (v : L → Lp ℝ 2 ν) :
    bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT
      (fun i => ∑ l, η l (g.nodeTime i) • v l)) =ᵐ[(volume.restrict (Ioc 0 T)).prod ν]
      fun z => finiteCellFunction g.physicalTimeCell (fun i => ∑ l, η l (g.nodeTime i)*v l z.2) z.1 := by
  have he i : (∑ l, η l (g.nodeTime i) • v l) =ᵐ[ν]
      fun x => ∑ l, η l (g.nodeTime i)*v l x := by
    apply (Lp.coeFn_finsetSum Finset.univ _).trans
    have hh := eventuallyEq_sum (s := Finset.univ) (fun l _ => Lp.coeFn_smul (η l (g.nodeTime i)) (v l))
    filter_upwards [hh] with x hx
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hx
  filter_upwards [bochnerL2ProductIsometry_fixed_time_ae T g hT _,
    quasiMeasurePreserving_snd.ae (Filter.eventually_all.mpr he)] with z hz hez
  rw [hz]
  unfold finiteCellFunction
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : z.1 ∈ g.physicalTimeCell i
  · simp only [Set.indicator_of_mem hi,
      Set.indicator_of_mem (show z∈Prod.fst ⁻¹' g.physicalTimeCell i from hi),hez i]
  · simp only [Set.indicator_of_notMem hi,
      Set.indicator_of_notMem (show z∉Prod.fst ⁻¹' g.physicalTimeCell i from hi)]

theorem finite_tensor_test_aestronglyMeasurable {S : Set (SpatialCoordinates d)}
    {L : Type*} [Fintype L] (T : ℝ) (η : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) :
    AEStronglyMeasurable (fun z : ℝ × SpatialCoordinates d => ∑ l, η l z.1*(ψ l).value z.2)
      ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)) := by
  apply Finset.aestronglyMeasurable_fun_sum
  intro l _
  exact (((hη l).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc |>.comp_quasiMeasurePreserving
    quasiMeasurePreserving_fst).mul
      ((ψ l).smooth.continuous.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_snd)

theorem bochner_finite_time_tensor_uniform_error {Ω L : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [SFinite ν] [Fintype L]
    (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (η : L → ℝ → ℝ) (ψ : L → Ω → ℝ) (v : L → Lp ℝ 2 ν)
    (A B ε : L → ℝ) (C : L → ℝ≥0)
    (hA : ∀ l, 0 ≤ A l) (ha : ∀ l t, t ∈ Icc 0 T → |η l t| ≤ A l)
    (hη : ∀ l, LipschitzOnWith (C l) (η l) (Icc 0 T))
    (hb : ∀ l, ∀ᵐ x ∂ν, |ψ l x| ≤ B l)
    (hv : ∀ l, ∀ᵐ x ∂ν, |v l x-ψ l x| ≤ ε l)
    (hψ : AEStronglyMeasurable (fun z : ℝ × Ω => ∑ l, η l z.1*ψ l z.2)
      ((volume.restrict (Ioc 0 T)).prod ν)) :
    eLpNorm (fun z => bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT
      (fun i => ∑ l, η l (g.nodeTime i) • v l)) z-∑ l, η l z.1*ψ l z.2) ⊤
      ((volume.restrict (Ioc 0 T)).prod ν) ≤
        ENNReal.ofReal (∑ l, (A l*ε l+(C l:ℝ)*g.dt*B l)) := by
  have hm := (Lp.aestronglyMeasurable (bochnerL2ProductIsometry
    (fixedTimeCellReconstruction T g hT (fun i => ∑ l, η l (g.nodeTime i) • v l)))).sub hψ
  change AEStronglyMeasurable (fun z => bochnerL2ProductIsometry
    (fixedTimeCellReconstruction T g hT (fun i => ∑ l, η l (g.nodeTime i) • v l)) z-
      ∑ l, η l z.1*ψ l z.2) _ at hm
  rw [eLpNorm_exponent_top hm]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [bochner_finite_time_tensor_ae T g hT η v,
    finite_time_tensor_uniform_error T g hT η ψ (fun l => v l) A B ε C hA ha hη hb hv] with z hz he
  simpa only [hz,Real.norm_eq_abs] using he


end Carleman
