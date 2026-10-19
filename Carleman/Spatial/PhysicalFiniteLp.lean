module

public import Carleman.Spatial.PhysicalFiniteSpace
public import Carleman.Spatial.AffineSimplexNorm
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! An exact counting-L² realization of the finite physical Hilbert norm. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace Carleman.PhysicalFiniteSpace
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {mass : ℝ} {hmass : 0 < mass}

theorem finiteMemLp (f : ι → ℝ) : MemLp f 2 Measure.count :=
  MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall fun i => norm_le_pi_norm f i)

def toCountLp (f : PhysicalFiniteSpace ι mass hmass) : Lp ℝ 2 (Measure.count : Measure ι) :=
  (finiteMemLp (fun i => Real.sqrt mass*f i)).toLp _

theorem toCountLp_apply (f : PhysicalFiniteSpace ι mass hmass) (i : ι) :
    toCountLp f i = Real.sqrt mass*f i :=
  Measure.ae_count_iff.mp (finiteMemLp (fun i => Real.sqrt mass*f i)).coeFn_toLp i

def toCountLpLinear : PhysicalFiniteSpace ι mass hmass →ₗ[ℝ] Lp ℝ 2 (Measure.count : Measure ι) where
  toFun := toCountLp
  map_add' f g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (toCountLp f) (toCountLp g)] with i hi
    rw [hi,Pi.add_apply,toCountLp_apply,toCountLp_apply,toCountLp_apply]
    exact mul_add _ _ _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul c (toCountLp f)] with i hi
    simp only [RingHom.id_apply]
    rw [hi,Pi.smul_apply,toCountLp_apply,toCountLp_apply]
    change Real.sqrt mass*(c*f i)=c*(Real.sqrt mass*f i)
    ring

theorem toCountLp_norm (f : PhysicalFiniteSpace ι mass hmass) : ‖toCountLp f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [lp_two_norm_sq_integral,integral_count,norm_sq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [toCountLp_apply,Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt hmass.le]

def countLpEquiv : PhysicalFiniteSpace ι mass hmass ≃ₗᵢ[ℝ] Lp ℝ 2 (Measure.count : Measure ι) :=
  LinearIsometryEquiv.ofSurjective
    { toCountLpLinear with norm_map' := toCountLp_norm } (by
      intro u
      let f : PhysicalFiniteSpace ι mass hmass :=
        valuesEquiv.symm (fun i => u i / Real.sqrt mass)
      refine ⟨f,?_⟩
      apply Lp.ext
      apply Filter.Eventually.of_forall
      intro i
      change toCountLp f i = u i
      rw [toCountLp_apply]
      change Real.sqrt mass*(u i / Real.sqrt mass)=u i
      field_simp [(Real.sqrt_pos.mpr hmass).ne'])

theorem countLpEquiv_apply (f : PhysicalFiniteSpace ι mass hmass) (i : ι) :
    countLpEquiv f i = Real.sqrt mass*f i := toCountLp_apply f i

end Carleman.PhysicalFiniteSpace
