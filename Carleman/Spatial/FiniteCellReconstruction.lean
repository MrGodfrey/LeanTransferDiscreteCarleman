module

public import Carleman.Spatial.PhysicalFiniteSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Actual piecewise-constant L² reconstruction on disjoint equal-mass cells, and its averaging adjoint. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {Ω ι : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
  [Fintype ι] (K : ι → Set Ω) (hK : ∀ i, MeasurableSet (K i))
  {mass : ℝ} (hm : 0 < mass)
attribute [local instance] Classical.propDecidable

def finiteCellLinear : PhysicalFiniteSpace ι mass hm →ₗ[ℝ] Lp ℝ 2 ν where
  toFun f := ∑ i, f i • indicatorConstLp 2 (hK i) (measure_ne_top ν _) (1:ℝ)
  map_add' f g := by
    change (∑ i, (f i+g i) • _) = _
    simp only [add_smul,Finset.sum_add_distrib]
  map_smul' c f := by
    change (∑ i, (c*f i) • _) = c • _
    simp only [mul_smul,Finset.smul_sum]

theorem finiteCellLinear_ae (f : PhysicalFiniteSpace ι mass hm) :
    finiteCellLinear (ν := ν) K hK hm f =ᵐ[ν] fun x => ∑ i, (K i).indicator (fun _ => f i) x := by
  apply (Lp.coeFn_finsetSum Finset.univ _).trans
  have hi (i : ι) : (fun x => (f i • indicatorConstLp 2 (hK i) (measure_ne_top ν _) (1:ℝ)) x)
      =ᵐ[ν] (K i).indicator (fun _ => f i) := by
    filter_upwards [Lp.coeFn_smul (f i) (indicatorConstLp 2 (hK i) (measure_ne_top ν _) (1:ℝ)),
      indicatorConstLp_coeFn (p := 2) (hs := hK i) (hμs := measure_ne_top ν _) (c := (1:ℝ))] with x hx he
    rw [hx]
    simp only [Pi.smul_apply,smul_eq_mul,he]
    by_cases hix : x ∈ K i <;> simp [hix]
  have hh := eventuallyEq_sum (s := Finset.univ) fun i _ => hi i
  filter_upwards [hh] with x hx
  simpa only [Finset.sum_apply] using hx

theorem finiteCellLinear_inner (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (hvol : ∀ i, ν.real (K i)=mass) (f g : PhysicalFiniteSpace ι mass hm) :
    inner ℝ (finiteCellLinear (ν := ν) K hK hm f) (finiteCellLinear (ν := ν) K hK hm g)=inner ℝ f g := by
  have hbasis (i j : ι) : inner ℝ (indicatorConstLp 2 (hK i) (measure_ne_top ν _) (1:ℝ))
      (indicatorConstLp 2 (hK j) (measure_ne_top ν _) (1:ℝ)) = if i=j then mass else 0 := by
    rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
    by_cases hij : i=j
    · subst j
      simp only [Set.inter_self,hvol,ite_true]
    · rw [Set.disjoint_iff_inter_eq_empty.mp (hdis hij)]
      simp only [Measure.real,measure_empty,ENNReal.toReal_zero,ite_eq_right hij]
  simp only [finiteCellLinear,LinearMap.coe_mk,AddHom.coe_mk,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right,hbasis,PhysicalFiniteSpace.inner_eq]
  simp only [mul_ite,mul_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

def finiteCellIsometry (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (hvol : ∀ i, ν.real (K i)=mass) : PhysicalFiniteSpace ι mass hm →ₗᵢ[ℝ] Lp ℝ 2 ν :=
  (finiteCellLinear (ν := ν) K hK hm).isometryOfInner (finiteCellLinear_inner K hK hm hdis hvol)

theorem finiteCellLinear_pairing (f : PhysicalFiniteSpace ι mass hm) (u : Lp ℝ 2 ν) :
    inner ℝ (finiteCellLinear (ν := ν) K hK hm f) u = ∑ i, f i*(∫ x in K i, u x ∂ν) := by
  simp only [finiteCellLinear,LinearMap.coe_mk,AddHom.coe_mk,sum_inner,real_inner_smul_left,
    L2.inner_indicatorConstLp_one]

theorem finiteCellIsometry_adjoint (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (hvol : ∀ i, ν.real (K i)=mass) (u : Lp ℝ 2 ν) (i : ι) :
    ((finiteCellIsometry K hK hm hdis hvol).toContinuousLinearMap.adjoint u) i =
      mass⁻¹*(∫ x in K i, u x ∂ν) := by
  let v : PhysicalFiniteSpace ι mass hm := PhysicalFiniteSpace.valuesEquiv.symm
    (fun j => mass⁻¹*(∫ x in K j, u x ∂ν))
  have he : (finiteCellIsometry K hK hm hdis hvol).toContinuousLinearMap.adjoint u = v := by
    apply ext_inner_left ℝ
    intro f
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℝ (finiteCellLinear (ν := ν) K hK hm f) u = inner ℝ f v
    rw [finiteCellLinear_pairing,PhysicalFiniteSpace.inner_eq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change f j*_ = mass*(f j*(mass⁻¹*_))
    field_simp [hm.ne']
  exact congrArg (fun z : PhysicalFiniteSpace ι mass hm => z i) he

theorem finiteCellIsometry_average_norm (hdis : Pairwise fun i j => Disjoint (K i) (K j))
    (hvol : ∀ i, ν.real (K i)=mass) (u : Lp ℝ 2 ν) :
    ‖(finiteCellIsometry K hK hm hdis hvol).toContinuousLinearMap.adjoint u‖ ≤ ‖u‖ := by
  let E := (finiteCellIsometry K hK hm hdis hvol).toContinuousLinearMap
  have hE : ‖E‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by change ‖(finiteCellIsometry K hK hm hdis hvol) f‖ ≤ 1*‖f‖; rw [LinearIsometry.norm_map,one_mul])
  have hA : ‖E.adjoint‖ ≤ 1 := by rwa [LinearIsometryEquiv.norm_map]
  exact (E.adjoint.le_opNorm u).trans (by simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hA (norm_nonneg u)))

end Carleman
