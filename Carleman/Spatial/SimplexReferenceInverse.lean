module

public import Carleman.Spatial.SimplexNodalLp
public import Carleman.Spatial.FirstOrderSobolevJet
public import Mathlib.Analysis.Calculus.FDeriv.Affine

/-! An actual inverse estimate on a fixed simplex, uniform over every
affine polynomial. Affine scaling and mesh-uniform shape bounds are separate. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

def simplexBarycentricDerivative (i : Fin (d+1)) : SpatialCoordinates d →L[ℝ] ℝ :=
  (⟨simplexBarycentric T i,(simplexBarycentric T i).continuous_of_finiteDimensional⟩ :
    SpatialCoordinates d →ᴬ[ℝ] ℝ).contLinear

def simplexNodalDerivativeLinear : (Fin (d+1) → ℝ) →ₗ[ℝ] (SpatialCoordinates d →L[ℝ] ℝ) where
  toFun c := ∑ i, c i • simplexBarycentricDerivative T i
  map_add' c e := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]
    rfl

theorem simplexNodalInterpolant_hasFDerivAt (c : Fin (d+1) → ℝ) (x : SpatialCoordinates d) :
    HasFDerivAt (simplexNodalInterpolant T c) (simplexNodalDerivativeLinear T c) x := by
  have hb (i : Fin (d+1)) : HasFDerivAt (simplexBarycentric T i) (simplexBarycentricDerivative T i) x :=
    (⟨simplexBarycentric T i,(simplexBarycentric T i).continuous_of_finiteDimensional⟩ :
      SpatialCoordinates d →ᴬ[ℝ] ℝ).hasFDerivAt
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hb i).const_smul (c i))
  convert h using 1
  · funext y
    exact simplexNodalInterpolant_apply T c y
  · rfl

def simplexNodalGradientLp (c : Fin (d+1) → ℝ) :
    Lp (DerivativeFiber d 1) 2 (volume.restrict (simplicialCell T.points)) :=
  (memLp_const (μ := volume.restrict (simplicialCell T.points)) (p := 2)
    (derivativeOneFiber (simplexNodalDerivativeLinear T c))).toLp
      (fun _ => derivativeOneFiber (simplexNodalDerivativeLinear T c))

theorem simplexNodalGradientLp_ae (c : Fin (d+1) → ℝ) :
    simplexNodalGradientLp T c =ᵐ[volume.restrict (simplicialCell T.points)]
      (fun x => derivativeOneFiber (fderiv ℝ (simplexNodalInterpolant T c) x)) := by
  have hh : simplexNodalGradientLp T c =ᵐ[volume.restrict (simplicialCell T.points)]
      (fun _ => derivativeOneFiber (simplexNodalDerivativeLinear T c)) := MemLp.coeFn_toLp _
  filter_upwards [hh] with x hx
  rw [hx,(simplexNodalInterpolant_hasFDerivAt T c x).fderiv]

def simplexNodalGradientLinear : (Fin (d+1) → ℝ) →ₗ[ℝ]
    Lp (DerivativeFiber d 1) 2 (volume.restrict (simplicialCell T.points)) where
  toFun := simplexNodalGradientLp T
  map_add' c e := by
    apply Lp.ext
    have hconst (b : Fin (d+1) → ℝ) : simplexNodalGradientLp T b =ᵐ[volume.restrict
      (simplicialCell T.points)] (fun _ => derivativeOneFiber (simplexNodalDerivativeLinear T b)) :=
      MemLp.coeFn_toLp _
    filter_upwards [hconst (c+e),hconst c,hconst e,
      Lp.coeFn_add (simplexNodalGradientLp T c) (simplexNodalGradientLp T e)] with x h1 h2 h3 h4
    rw [h1,h4,Pi.add_apply,h2,h3,map_add,map_add]
  map_smul' r c := by
    change simplexNodalGradientLp T (r • c) = r • simplexNodalGradientLp T c
    apply Lp.ext
    have hconst (b : Fin (d+1) → ℝ) : simplexNodalGradientLp T b =ᵐ[volume.restrict
      (simplicialCell T.points)] (fun _ => derivativeOneFiber (simplexNodalDerivativeLinear T b)) :=
      MemLp.coeFn_toLp _
    filter_upwards [hconst (r • c),hconst c,Lp.coeFn_smul r (simplexNodalGradientLp T c)] with x h1 h2 h3
    rw [h1,h3,Pi.smul_apply,h2,map_smul,map_smul]

theorem simplex_reference_inverse : ∃ C > (0:ℝ), ∀ c : Fin (d+1) → ℝ,
    ‖simplexNodalGradientLp T c‖ ≤ C*‖simplexNodalLp T c‖ := by
  obtain ⟨B,hB,hbound⟩ := simplexNodalLp_coefficient_bound T
  let G := (simplexNodalGradientLinear T).toContinuousLinearMap
  refine ⟨‖G‖*B+1,by positivity,?_⟩
  intro c
  calc
    ‖simplexNodalGradientLp T c‖ = ‖G c‖ := rfl
    _ ≤ ‖G‖*‖c‖ := G.le_opNorm c
    _ ≤ ‖G‖*(B*‖simplexNodalLp T c‖) := mul_le_mul_of_nonneg_left (hbound c) (norm_nonneg G)
    _ ≤ (‖G‖*B+1)*‖simplexNodalLp T c‖ := by nlinarith [norm_nonneg (simplexNodalLp T c)]

end Carleman
