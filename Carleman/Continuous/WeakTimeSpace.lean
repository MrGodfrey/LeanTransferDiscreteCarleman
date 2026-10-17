module

public import Carleman.Continuous.L2Pairing
public import Carleman.Spatial.WeakDerivativeUnique

/-! The actual vector-valued weak time derivative is a closed relation on
Bochner L² classes, with uniqueness. No pointwise derivative is postulated. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem HasWeakTimeDerivative.congr_derivative {g : TimeGrid} {u du dv : ℝ → H}
    (hu : HasWeakTimeDerivative g u du) (hd : du =ᵐ[g.timeMeasure] dv) :
    HasWeakTimeDerivative g u dv := by
  intro φ hs hc hsup
  rw [hu φ hs hc hsup]
  congr 1
  apply integral_congr_ae
  filter_upwards [hd] with t ht
  rw [ht]

/-- All smooth compactly supported scalar tests and all H directions. -/
def IsWeakTimeClass (g : TimeGrid) (u du : Lp H 2 g.timeMeasure) : Prop :=
  ∀ (φ : SpatialTest (Ioo 0 g.period)) (h : H),
    inner ℝ u (scalarTensor g.timeMeasure (φ.derivativeLp g.timeMeasure 1) h) =
      -inner ℝ du (scalarTensor g.timeMeasure (φ.toLp g.timeMeasure) h)

namespace IsWeakTimeClass
variable {g : TimeGrid} {u v du dv : Lp H 2 g.timeMeasure}

theorem zero : IsWeakTimeClass g (0 : Lp H 2 g.timeMeasure) 0 := by
  intro φ h
  simp

theorem add (hu : IsWeakTimeClass g u du) (hv : IsWeakTimeClass g v dv) :
    IsWeakTimeClass g (u+v) (du+dv) := by
  intro φ h
  rw [inner_add_left, inner_add_left, hu φ h, hv φ h]
  ring

theorem smul (hu : IsWeakTimeClass g u du) (c : ℝ) :
    IsWeakTimeClass g (c • u) (c • du) := by
  intro φ h
  rw [real_inner_smul_left, real_inner_smul_left, hu φ h]
  ring

variable [CompleteSpace H]

/-- Equality with the original H-valued distributional derivative interface. -/
theorem iff_weakDerivative : IsWeakTimeClass g u du ↔ HasWeakTimeDerivative g u du := by
  have hi : ∀ (z : Lp H 2 g.timeMeasure) (φ : SpatialTest (Ioo 0 g.period)) (h : H),
      inner ℝ z (scalarTensor g.timeMeasure (φ.toLp g.timeMeasure) h) =
        inner ℝ (∫ t, φ.value t • z t ∂g.timeMeasure) h := by
    intro z φ h
    rw [inner_scalarTensor_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [φ.toLp_ae g.timeMeasure] with t ht
    rw [ht]
  have hd : ∀ (z : Lp H 2 g.timeMeasure) (φ : SpatialTest (Ioo 0 g.period)) (h : H),
      inner ℝ z (scalarTensor g.timeMeasure (φ.derivativeLp g.timeMeasure 1) h) =
        inner ℝ (∫ t, deriv φ.value t • z t ∂g.timeMeasure) h := by
    intro z φ h
    rw [inner_scalarTensor_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [φ.derivativeLp_ae g.timeMeasure 1] with t ht
    rw [ht]
    rfl
  constructor
  · intro hw φ hs hc hsup
    let ψ : SpatialTest (Ioo 0 g.period) := ⟨φ, hs, hc, hsup⟩
    apply ext_inner_right ℝ
    intro h
    simpa only [hd, hi, inner_neg_left] using hw ψ h
  · intro hw φ h
    rw [hd, hi, hw φ.value φ.smooth φ.compact φ.support, inner_neg_left]

/-- Vector L² functions are determined by genuine compactly supported tests. -/
theorem eq_zero_of_tests (v : Lp H 2 g.timeMeasure)
    (hv : ∀ (φ : SpatialTest (Ioo 0 g.period)) (h : H),
      inner ℝ v (scalarTensor g.timeMeasure (φ.toLp g.timeMeasure) h) = 0) : v = 0 := by
  have ha := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((Lp.memLp v).locallyIntegrable (by norm_num)).locallyIntegrableOn (Ioo 0 g.period))
    (fun φ hs hc hsup => by
      let ψ : SpatialTest (Ioo 0 g.period) := ⟨φ, hs, hc, hsup⟩
      apply ext_inner_right ℝ
      intro h
      have he := hv ψ h
      rw [inner_scalarTensor_integral] at he
      rw [inner_zero_left]
      convert he using 2
      apply integral_congr_ae
      filter_upwards [ψ.toLp_ae g.timeMeasure] with t ht
      rw [ht])
  apply Lp.ext
  filter_upwards [ha, ae_restrict_mem measurableSet_Ioo,
    Lp.coeFn_zero (E := H) (p := 2) (μ := g.timeMeasure)] with t ht hmem hz
  exact (ht hmem).trans hz.symm

theorem unique (hu : IsWeakTimeClass g u du) (hv : IsWeakTimeClass g u dv) : du = dv := by
  apply sub_eq_zero.mp
  apply eq_zero_of_tests
  intro φ h
  rw [inner_sub_left]
  have h₁ := hu φ h
  have h₂ := hv φ h
  linarith
end IsWeakTimeClass

/-- The genuine distributional graph in the product of two Bochner spaces. -/
def weakTimeSubmodule (g : TimeGrid) : Submodule ℝ (Lp H 2 g.timeMeasure × Lp H 2 g.timeMeasure) where
  carrier := {p | IsWeakTimeClass g p.1 p.2}
  zero_mem' := IsWeakTimeClass.zero
  add_mem' := fun hu hv => hu.add hv
  smul_mem' := fun c _ hu => hu.smul c

theorem weakTimeSubmodule_isClosed (g : TimeGrid) :
    IsClosed (weakTimeSubmodule (H := H) g : Set (Lp H 2 g.timeMeasure × Lp H 2 g.timeMeasure)) := by
  change IsClosed {p : Lp H 2 g.timeMeasure × Lp H 2 g.timeMeasure |
    ∀ (φ : SpatialTest (Ioo 0 g.period)) (h : H),
      inner ℝ p.1 (scalarTensor g.timeMeasure (φ.derivativeLp g.timeMeasure 1) h) =
        -inner ℝ p.2 (scalarTensor g.timeMeasure (φ.toLp g.timeMeasure) h)}
  simp only [ofPred_forall]
  exact isClosed_iInter fun φ => isClosed_iInter fun h =>
    isClosed_eq (continuous_fst.inner continuous_const) (continuous_snd.inner continuous_const).neg

instance weakTimeSubmodule_completeSpace [CompleteSpace H] (g : TimeGrid) :
    CompleteSpace (weakTimeSubmodule (H := H) g) := by
  let : IsClosed (weakTimeSubmodule (H := H) g :
    Set (Lp H 2 g.timeMeasure × Lp H 2 g.timeMeasure)) := weakTimeSubmodule_isClosed g
  exact IsClosed.completeSpace_coe
end Carleman
