module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Integral.Prod

/-! Actual scalar product representatives of L²-valued simple functions, with Fubini norm identity. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators Topology
namespace Carleman
local infixr:25 " →ₛ " => SimpleFunc
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]

theorem simpleL2_uncurry_memLp (f : α →ₛ Lp ℝ 2 ν) :
    MemLp (fun z : α × β => (f z.1) z.2) 2 (μ.prod ν) := by
  classical
  have he : (fun z : α × β => (f z.1) z.2) =
      fun z => ∑ v ∈ f.range, (Prod.fst ⁻¹' (f ⁻¹' {v})).indicator (fun z => v z.2) z := by
    funext z
    rw [Finset.sum_eq_single (f z.1)]
    · simp
    · intro v _ hv
      exact Set.indicator_of_notMem (by simpa only [mem_preimage,mem_singleton_iff] using Ne.symm hv) _
    · exact fun hn => False.elim (hn (f.mem_range_self z.1))
  rw [he]
  apply memLp_finsetSum
  intro v _
  exact ((Lp.memLp v).comp_snd μ).indicator ((f.measurableSet_fiber v).preimage measurable_fst).nullMeasurableSet

def simpleL2_product (f : α →ₛ Lp ℝ 2 ν) : Lp ℝ 2 (μ.prod ν) :=
  (simpleL2_uncurry_memLp f).toLp (fun z => (f z.1) z.2)

omit [IsFiniteMeasure μ] [SFinite ν] in
theorem simpleL2_uncurry_add_ae (f g : α →ₛ Lp ℝ 2 ν) :
    (fun z : α × β => ((f+g) z.1) z.2) =ᵐ[μ.prod ν]
      fun z => (f z.1) z.2+(g z.1) z.2 := by
  have he : ∀ᵐ x ∂ν, ∀ v ∈ f.range, ∀ w ∈ g.range, (v+w : Lp ℝ 2 ν) x=v x+w x := by
    apply (Filter.eventually_all_finset _).mpr
    intro v _
    apply (Filter.eventually_all_finset _).mpr
    intro w _
    exact Lp.coeFn_add v w
  filter_upwards [quasiMeasurePreserving_snd.ae he] with z hz
  exact hz (f z.1) (f.mem_range_self z.1) (g z.1) (g.mem_range_self z.1)

omit [IsFiniteMeasure μ] [SFinite ν] in
theorem simpleL2_uncurry_smul_ae (c : ℝ) (f : α →ₛ Lp ℝ 2 ν) :
    (fun z : α × β => ((c • f) z.1) z.2) =ᵐ[μ.prod ν]
      fun z => c • (f z.1) z.2 := by
  have he : ∀ᵐ x ∂ν, ∀ v ∈ f.range, (c • v : Lp ℝ 2 ν) x=c • v x := by
    apply (Filter.eventually_all_finset _).mpr
    intro v _
    exact Lp.coeFn_smul c v
  filter_upwards [quasiMeasurePreserving_snd.ae he] with z hz
  exact hz (f z.1) (f.mem_range_self z.1)

def simpleL2_productLinear : (α →ₛ Lp ℝ 2 ν) →ₗ[ℝ] Lp ℝ 2 (μ.prod ν) where
  toFun := simpleL2_product
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(simpleL2_uncurry_memLp (f+g)).coeFn_toLp,
      Lp.coeFn_add (simpleL2_product f) (simpleL2_product g),
      (simpleL2_uncurry_memLp f).coeFn_toLp,(simpleL2_uncurry_memLp g).coeFn_toLp,
      simpleL2_uncurry_add_ae (μ := μ) f g] with z hs ha hf hg he
    exact hs.trans (he.trans (ha.trans (congrArg₂ (·+·) hf hg)).symm)
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(simpleL2_uncurry_memLp (c • f)).coeFn_toLp,
      Lp.coeFn_smul c (simpleL2_product f),(simpleL2_uncurry_memLp f).coeFn_toLp,
      simpleL2_uncurry_smul_ae (μ := μ) c f] with z hs ha hf he
    exact hs.trans (he.trans (ha.trans (congrArg (c • ·) hf)).symm)

def simpleL2_bochnerLinear : (α →ₛ Lp ℝ 2 ν) →ₗ[ℝ] Lp (Lp ℝ 2 ν) 2 μ where
  toFun f := (f.memLp_of_isFiniteMeasure 2 μ).toLp f
  map_add' f g := by exact MemLp.toLp_add _ _
  map_smul' c f := by exact MemLp.toLp_const_smul c _

omit [IsFiniteMeasure μ] [SFinite ν] in
theorem memLp_toLp_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : α → H) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2=∫ t, ‖f t‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht,real_inner_self_eq_norm_sq]

theorem simpleL2_product_norm (f : α →ₛ Lp ℝ 2 ν) :
    ‖simpleL2_product (μ := μ) f‖=‖simpleL2_bochnerLinear (μ := μ) f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(simpleL2_uncurry_memLp f).toLp _‖^2=
    ‖(f.memLp_of_isFiniteMeasure 2 μ).toLp f‖^2
  rw [memLp_toLp_norm_sq,memLp_toLp_norm_sq]
  rw [integral_prod _ ((memLp_two_iff_integrable_sq_norm
    (simpleL2_uncurry_memLp f).aestronglyMeasurable).mp (simpleL2_uncurry_memLp f))]
  apply integral_congr_ae
  filter_upwards [] with t
  have hv := memLp_toLp_norm_sq (f t : β → ℝ) (Lp.memLp (f t))
  rw [Lp.toLp_coeFn] at hv
  exact hv.symm

omit [SFinite ν] in
theorem simpleL2_bochnerLinear_dense :
    DenseRange (simpleL2_bochnerLinear (μ := μ) (ν := ν)) := by
  have hd := Lp.simpleFunc.denseRange (E := Lp ℝ 2 ν) (μ := μ) (by norm_num : (2:ENNReal)≠⊤)
  intro u
  apply closure_mono (t := Set.range (simpleL2_bochnerLinear (μ := μ) (ν := ν))) ?_ (hd u)
  rintro _ ⟨v,rfl⟩
  refine ⟨Lp.simpleFunc.toSimpleFunc v,?_⟩
  exact congrArg (fun w : Lp.simpleFunc (Lp ℝ 2 ν) 2 μ => (w : Lp (Lp ℝ 2 ν) 2 μ))
    (Lp.simpleFunc.toLp_toSimpleFunc v)

end Carleman
