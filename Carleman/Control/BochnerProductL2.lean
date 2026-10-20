module

public import Carleman.Control.SimpleL2Product
public import Carleman.Control.TimeWeakTesting
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The genuine isometric map from Bochner L² to product L², extended from actual simple representatives. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators Topology
namespace Carleman
local infixr:25 " →ₛ " => SimpleFunc
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]

def bochnerL2ProductIsometry : Lp (Lp ℝ 2 ν) 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod ν) :=
  (simpleL2_productLinear (μ := μ) (ν := ν)).extendOfIsometry
    simpleL2_bochnerLinear_dense simpleL2_product_norm

theorem bochnerL2ProductIsometry_simple (f : α →ₛ Lp ℝ 2 ν) :
    bochnerL2ProductIsometry (simpleL2_bochnerLinear (μ := μ) f)=simpleL2_product f :=
  LinearMap.extendOfIsometry_eq _ _ _ f

theorem bochnerL2ProductIsometry_simple_ae (f : α →ₛ Lp ℝ 2 ν) :
    bochnerL2ProductIsometry (simpleL2_bochnerLinear (μ := μ) f) =ᵐ[μ.prod ν]
      fun z => (f z.1) z.2 := by
  rw [bochnerL2ProductIsometry_simple]
  exact (simpleL2_uncurry_memLp f).coeFn_toLp

theorem bochnerL2ProductIsometry_indicator_ae {s : Set α} (hs : MeasurableSet s)
    (v : Lp ℝ 2 ν) :
    bochnerL2ProductIsometry (indicatorConstLp 2 hs (measure_ne_top μ s) v) =ᵐ[μ.prod ν]
      (Prod.fst ⁻¹' s).indicator (fun z => v z.2) := by
  classical
  let f : α →ₛ Lp ℝ 2 ν := SimpleFunc.piecewise s hs (SimpleFunc.const α v) (SimpleFunc.const α 0)
  have hf : simpleL2_bochnerLinear (μ := μ) f=indicatorConstLp 2 hs (measure_ne_top μ s) v := by
    apply Lp.ext
    filter_upwards [(f.memLp_of_isFiniteMeasure 2 μ).coeFn_toLp,
      (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := v))] with t ht hi
    calc
      _ = f t := ht
      _ = s.indicator (fun _ => v) t := by
        by_cases hts : t∈s <;> simp [f,SimpleFunc.piecewise_apply,hts]
      _ = _ := hi.symm
  rw [← hf]
  filter_upwards [bochnerL2ProductIsometry_simple_ae (μ := μ) f,
    quasiMeasurePreserving_snd.ae (Lp.coeFn_zero ℝ 2 ν)] with z hz hzero
  rw [hz]
  by_cases hzs : z.1∈s
  · simp [f,SimpleFunc.piecewise_apply,hzs]
  · simpa [f,SimpleFunc.piecewise_apply,hzs] using hzero

theorem bochnerL2ProductIsometry_weak
    (u : ℕ → Lp (Lp ℝ 2 ν) 2 μ) (y : Lp (Lp ℝ 2 ν) 2 μ)
    (hu : ∀ w, Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ y w))) :
    ∀ w : Lp ℝ 2 (μ.prod ν), Tendsto
      (fun n => inner ℝ (bochnerL2ProductIsometry (u n)) w) atTop
      (𝓝 (inner ℝ (bochnerL2ProductIsometry y) w)) := by
  intro w
  simpa only [ContinuousLinearMap.adjoint_inner_right,LinearIsometry.coe_toContinuousLinearMap] using
    hu (bochnerL2ProductIsometry.toContinuousLinearMap.adjoint w)

end Carleman

namespace Carleman
theorem bochnerL2ProductIsometry_time_ae {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [SFinite ν] (g : TimeGrid) (u : Fin g.steps → Lp ℝ 2 ν) :
    bochnerL2ProductIsometry (timeCellReconstruction g u) =ᵐ[(volume.restrict (Ioc 0 g.period)).prod ν]
      fun z => ∑ i, (Prod.fst ⁻¹' g.physicalTimeCell i).indicator (fun z => (u i) z.2) z := by
  classical
  rw [timeCellReconstruction,_root_.map_sum]
  apply (Lp.coeFn_finsetSum Finset.univ _).trans
  have hh := eventuallyEq_sum (s := Finset.univ) (fun i _ =>
    bochnerL2ProductIsometry_indicator_ae
      (μ := volume.restrict (Ioc 0 g.period)) (show MeasurableSet (g.physicalTimeCell i) from measurableSet_Ioc) (u i))
  filter_upwards [hh] with z hz
  simpa only [Finset.sum_apply] using hz

theorem bochnerL2ProductIsometry_fixed_time_ae {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [SFinite ν] (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (u : Fin g.steps → Lp ℝ 2 ν) :
    bochnerL2ProductIsometry (fixedTimeCellReconstruction T g hT u) =ᵐ[(volume.restrict (Ioc 0 T)).prod ν]
      fun z => ∑ i, (Prod.fst ⁻¹' g.physicalTimeCell i).indicator (fun z => (u i) z.2) z := by
  subst T
  exact bochnerL2ProductIsometry_time_ae g u

end Carleman

