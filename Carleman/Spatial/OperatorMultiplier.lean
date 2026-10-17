module

public import Carleman.Spatial.WeightedL2
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! Bounded measurable coefficients acting on genuine vector-valued L² fields.
Scalar weights commute with the pointwise linear coefficient. This supports
finite collections of spatial derivatives with their Euclidean fiber norms. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure OperatorMultiplier (ν : Measure Ω) (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  value : Ω → E →L[ℝ] F
  measurable : AEStronglyMeasurable value ν
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounded : ∀ᵐ x ∂ν, ‖value x‖ ≤ bound

namespace OperatorMultiplier
variable {ν : Measure Ω} (a : OperatorMultiplier ν E F)

theorem memLp_apply (u : Lp E 2 ν) : MemLp (fun x => a.value x (u x)) 2 ν := by
  apply (Lp.memLp u).of_le_mul (c := a.bound)
    ((ContinuousLinearMap.id ℝ (E →L[ℝ] F)).aestronglyMeasurable_comp₂
      a.measurable (Lp.aestronglyMeasurable u))
  filter_upwards [a.bounded] with x hx
  exact (a.value x).le_of_opNorm_le hx (u x)

def map (u : Lp E 2 ν) : Lp F 2 ν := (a.memLp_apply u).toLp (fun x => a.value x (u x))

theorem map_ae (u : Lp E 2 ν) : a.map u =ᵐ[ν] (fun x => a.value x (u x)) :=
  (a.memLp_apply u).coeFn_toLp

theorem map_add (u v : Lp E 2 ν) : a.map (u+v) = a.map u + a.map v := by
  apply Lp.ext
  filter_upwards [a.map_ae (u+v), a.map_ae u, a.map_ae v,
    Lp.coeFn_add u v, Lp.coeFn_add (a.map u) (a.map v)] with x h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5
  rw [h1, h5, h2, h3, h4, _root_.map_add]

theorem map_smul (c : ℝ) (u : Lp E 2 ν) : a.map (c • u) = c • a.map u := by
  apply Lp.ext
  filter_upwards [a.map_ae (c • u), a.map_ae u, Lp.coeFn_smul c u,
    Lp.coeFn_smul c (a.map u)] with x h1 h2 h3 h4
  simp only [Pi.smul_apply] at h3 h4
  rw [h1, h4, h2, h3, _root_.map_smul]

def linearMap : Lp E 2 ν →ₗ[ℝ] Lp F 2 ν where
  toFun := a.map
  map_add' := a.map_add
  map_smul' := a.map_smul

theorem norm_map_le (u : Lp E 2 ν) : ‖a.map u‖ ≤ a.bound * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [a.map_ae u, a.bounded] with x hx ha
  rw [hx]
  exact (a.value x).le_of_opNorm_le ha (u x)

def continuousLinearMap : Lp E 2 ν →L[ℝ] Lp F 2 ν :=
  a.linearMap.mkContinuous a.bound a.norm_map_le

/-- Pointwise spatial coefficients commute with every scalar weight. -/
theorem map_weight (w : BoundedMultiplier ν) (u : Lp E 2 ν) :
    a.map (w.map u) = w.map (a.map u) := by
  apply Lp.ext
  filter_upwards [a.map_ae (w.map u), w.map_ae u,
    w.map_ae (a.map u), a.map_ae u] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, _root_.map_smul]

theorem weighted_seminorm_le (w : BoundedMultiplier ν) (u : Lp E 2 ν) :
    w.seminorm (a.map u) ≤ a.bound * w.seminorm u := by
  simp only [BoundedMultiplier.seminorm_apply, ← a.map_weight]
  exact a.norm_map_le (w.map u)

end OperatorMultiplier
end Carleman

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman.OperatorMultiplier
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] {ν : Measure Ω}

/-- A finite list of ordinary scalar bounded coefficients becomes the genuine
pointwise linear expression sum_i a_i(x) v_i on the Euclidean derivative fiber. -/
def ofCoefficients (a : I → BoundedMultiplier ν) :
    OperatorMultiplier ν (EuclideanSpace ℝ I) ℝ where
  value x := ∑ i, (a i).value x • EuclideanSpace.proj i
  measurable := Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
    (a i).measurable.smul_const (EuclideanSpace.proj i)
  bound := ∑ i, (a i).bound
  bound_nonneg := Finset.sum_nonneg fun i _ => (a i).bound_nonneg
  bounded := by
    filter_upwards [ae_all_iff.mpr (fun i => (a i).bounded)] with x hx
    calc
      _ ≤ ∑ i, ‖(a i).value x • EuclideanSpace.proj (𝕜 := ℝ) i‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs]
        have hp : ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 := by
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro v
          change ‖v i‖ ≤ 1 * ‖v‖
          simpa only [one_mul] using PiLp.norm_apply_le (p := 2) v i
        exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans (by simpa using hx i)

theorem ofCoefficients_apply (a : I → BoundedMultiplier ν) (x : Ω)
    (v : EuclideanSpace ℝ I) :
    (ofCoefficients a).value x v = ∑ i, (a i).value x * v i := by
  simp only [ofCoefficients, sum_apply, smul_apply,
    EuclideanSpace.coe_proj, smul_eq_mul]

theorem ofCoefficients_map_ae (a : I → BoundedMultiplier ν)
    (u : Lp (EuclideanSpace ℝ I) 2 ν) :
    (ofCoefficients a).map u =ᵐ[ν] (fun x => ∑ i, (a i).value x * u x i) := by
  simpa only [ofCoefficients_apply] using (ofCoefficients a).map_ae u
end Carleman.OperatorMultiplier

@[expose] public noncomputable section
namespace Carleman.OperatorMultiplier
open MeasureTheory
variable {Ω E F : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def const (A : E →L[ℝ] F) : OperatorMultiplier ν E F where
  value := fun _ => A
  measurable := aestronglyMeasurable_const
  bound := ‖A‖
  bound_nonneg := norm_nonneg A
  bounded := Filter.Eventually.of_forall fun _ => le_rfl

theorem const_map_ae (A : E →L[ℝ] F) (u : Lp E 2 ν) :
    (const (ν := ν) A).map u =ᵐ[ν] (fun x => A (u x)) := (const A).map_ae u
end Carleman.OperatorMultiplier

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman
variable {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ordinary bounded measurable vector coefficients, including the coordinate
vectors that realize the gradient in the heat-equation application. -/
structure VectorCoefficient (ν : Measure Ω) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  value : Ω → F
  measurable : AEStronglyMeasurable value ν
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounded : ∀ᵐ x ∂ν, ‖value x‖ ≤ bound

namespace OperatorMultiplier
variable {ν : Measure Ω} {I : Type*} [Fintype I]

/-- Finite ordinary vector coefficients produce the pointwise differential
expression sum_i v_i • a_i(x); no scalar-output restriction. -/
def ofVectorCoefficients (a : I → VectorCoefficient ν F) :
    OperatorMultiplier ν (EuclideanSpace ℝ I) F where
  value x := ∑ i, (EuclideanSpace.proj i).smulRight ((a i).value x)
  measurable := Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ I) F (EuclideanSpace.proj i)).continuous.comp_aestronglyMeasurable
      (a i).measurable
  bound := ∑ i, (a i).bound
  bound_nonneg := Finset.sum_nonneg fun i _ => (a i).bound_nonneg
  bounded := by
    filter_upwards [ae_all_iff.mpr (fun i => (a i).bounded)] with x hx
    calc
      _ ≤ ∑ i, ‖(EuclideanSpace.proj (𝕜 := ℝ) i).smulRight ((a i).value x)‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [ContinuousLinearMap.norm_smulRight_apply]
        have hp : ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 := by
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro v
          change ‖v i‖ ≤ 1 * ‖v‖
          simpa only [one_mul] using PiLp.norm_apply_le (p := 2) v i
        exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (by simpa using hx i)

theorem ofVectorCoefficients_apply (a : I → VectorCoefficient ν F) (x : Ω)
    (v : EuclideanSpace ℝ I) :
    (ofVectorCoefficients a).value x v = ∑ i, v i • (a i).value x := by
  simp only [ofVectorCoefficients, sum_apply, ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj]

theorem ofVectorCoefficients_map_ae (a : I → VectorCoefficient ν F)
    (u : Lp (EuclideanSpace ℝ I) 2 ν) :
    (ofVectorCoefficients a).map u =ᵐ[ν] (fun x => ∑ i, u x i • (a i).value x) := by
  simpa only [ofVectorCoefficients_apply] using (ofVectorCoefficients a).map_ae u
end OperatorMultiplier
end Carleman
