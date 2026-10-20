module
public import Carleman.Spatial.WeightedHessianIdentity
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
/-! Actual smooth level cutoffs, their boundary layer and exact chain rule. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem smoothTransition_deriv_zero_of_nonpos {t : ℝ} (ht : t≤0) :
    deriv Real.smoothTransition t=0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Eventually.of_forall fun y => by
    rw [Real.smoothTransition.zero_of_nonpos ht]
    exact Real.smoothTransition.nonneg y

theorem smoothTransition_deriv_zero_of_one_le {t : ℝ} (ht : 1≤t) :
    deriv Real.smoothTransition t=0 := by
  apply IsLocalMax.deriv_eq_zero
  exact Eventually.of_forall fun y => by
    rw [Real.smoothTransition.one_of_one_le ht]
    exact Real.smoothTransition.le_one y

def levelCutoff (g : SpatialCoordinates d → ℝ) (a ε : ℝ) (x : SpatialCoordinates d) : ℝ :=
  Real.smoothTransition ((a-g x-ε)/ε)

def levelLayerWeight (g : SpatialCoordinates d → ℝ) (a ε : ℝ) (x : SpatialCoordinates d) : ℝ :=
  deriv Real.smoothTransition ((a-g x-ε)/ε)/ε

theorem levelCutoff_contDiff (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g) (a ε : ℝ) :
    ContDiff ℝ ∞ (levelCutoff g a ε) :=
  Real.smoothTransition.contDiff.comp (((contDiff_const.sub hg).sub contDiff_const).div_const ε)

theorem levelLayerWeight_contDiff (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g) (a ε : ℝ) :
    ContDiff ℝ ∞ (levelLayerWeight g a ε) := by
  have hd : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  exact (hd.comp (((contDiff_const.sub hg).sub contDiff_const).div_const ε)).div_const ε

theorem levelCutoff_bounds (g : SpatialCoordinates d → ℝ) (a ε : ℝ) (x : SpatialCoordinates d) :
    0≤levelCutoff g a ε x ∧ levelCutoff g a ε x≤1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem levelLayerWeight_nonneg (g : SpatialCoordinates d → ℝ) (a : ℝ) {ε : ℝ}
    (hε : 0<ε) (x : SpatialCoordinates d) : 0≤levelLayerWeight g a ε x :=
  div_nonneg Real.smoothTransition.monotone.deriv_nonneg hε.le

theorem levelCutoff_zero (g : SpatialCoordinates d → ℝ) (a : ℝ) {ε : ℝ}
    (hε : 0<ε) (x : SpatialCoordinates d) (hx : a-ε≤g x) :
    levelCutoff g a ε x=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

theorem levelCutoff_one (g : SpatialCoordinates d → ℝ) (a : ℝ) {ε : ℝ}
    (hε : 0<ε) (x : SpatialCoordinates d) (hx : g x≤a-2*ε) :
    levelCutoff g a ε x=1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ hε).mpr
  linarith

theorem levelLayerWeight_zero_outer (g : SpatialCoordinates d → ℝ) (a : ℝ) {ε : ℝ}
    (hε : 0<ε) (x : SpatialCoordinates d) (hx : a-ε≤g x) :
    levelLayerWeight g a ε x=0 := by
  rw [levelLayerWeight,smoothTransition_deriv_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le),zero_div]

theorem levelLayerWeight_zero_inner (g : SpatialCoordinates d → ℝ) (a : ℝ) {ε : ℝ}
    (hε : 0<ε) (x : SpatialCoordinates d) (hx : g x≤a-2*ε) :
    levelLayerWeight g a ε x=0 := by
  have ht : 1≤(a-g x-ε)/ε := (le_div_iff₀ hε).mpr (by linarith)
  rw [levelLayerWeight,smoothTransition_deriv_zero_of_one_le ht,zero_div]

theorem levelCutoff_fderiv (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g)
    (a ε : ℝ) (x : SpatialCoordinates d) :
    fderiv ℝ (levelCutoff g a ε) x=(-levelLayerWeight g a ε x) • fderiv ℝ g x := by
  have hA : HasFDerivAt (fun y => (a-g y-ε)/ε) (ε⁻¹ • (-fderiv ℝ g x)) x := by
    simpa only [div_eq_mul_inv] using
      (((hg.differentiable (by simp) x).hasFDerivAt.const_sub a).sub_const ε).mul_const ε⁻¹
  have hT : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition ((a-g x-ε)/ε)) ((a-g x-ε)/ε) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp) _).hasDerivAt
  have he := hT.comp_hasFDerivAt x hA
  change fderiv ℝ (Real.smoothTransition ∘ (fun y => (a-g y-ε)/ε)) x=_
  rw [he.fderiv]
  ext v
  simp only [smul_apply,smul_eq_mul,neg_apply,levelLayerWeight]
  ring

theorem levelCutoff_tsupport (g : SpatialCoordinates d → ℝ) (hg : Continuous g)
    (a : ℝ) {ε : ℝ} (hε : 0<ε) :
    tsupport (levelCutoff g a ε) ⊆ {x | g x≤a-ε} := by
  apply closure_minimal _ (isClosed_le hg continuous_const)
  intro x hx
  by_contra hn
  exact hx (levelCutoff_zero g a hε x (le_of_not_ge hn))

theorem levelLayerWeight_tsupport (g : SpatialCoordinates d → ℝ) (hg : Continuous g)
    (a : ℝ) {ε : ℝ} (hε : 0<ε) :
    tsupport (levelLayerWeight g a ε) ⊆ {x | a-2*ε≤g x ∧ g x≤a-ε} := by
  apply closure_minimal _ ((isClosed_le continuous_const hg).inter (isClosed_le hg continuous_const))
  intro x hx
  constructor
  · by_contra hn
    exact hx (levelLayerWeight_zero_inner g a hε x (le_of_not_ge hn))
  · by_contra hn
    exact hx (levelLayerWeight_zero_outer g a hε x (le_of_not_ge hn))

theorem levelCutoff_compact (g : SpatialCoordinates d → ℝ) (hg : Continuous g)
    (a : ℝ) (hK : IsCompact (closure {x | g x<a})) {ε : ℝ} (hε : 0<ε) :
    HasCompactSupport (levelCutoff g a ε) := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  apply subset_closure
  have he := levelCutoff_tsupport g hg a hε hx
  change g x≤a-ε at he
  change g x<a
  linarith

theorem levelLayerWeight_compact (g : SpatialCoordinates d → ℝ) (hg : Continuous g)
    (a : ℝ) (hK : IsCompact (closure {x | g x<a})) {ε : ℝ} (hε : 0<ε) :
    HasCompactSupport (levelLayerWeight g a ε) := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  apply subset_closure
  have he := (levelLayerWeight_tsupport g hg a hε hx).2
  change g x<a
  linarith

theorem levelCutoff_tendsto (g : SpatialCoordinates d → ℝ) (a : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0<ε n) (ht : Tendsto ε atTop (𝓝 0)) (x : SpatialCoordinates d) :
    Tendsto (fun n => levelCutoff g a (ε n) x) atTop (𝓝 ({y | g y<a}.indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : g x<a
  · rw [indicator_of_mem (show x∈{y | g y<a} from hx)]
    have hh : ∀ᶠ n in atTop, 2*ε n<a-g x :=
      (ht.const_mul 2).eventually (gt_mem_nhds (by simpa using sub_pos.mpr hx))
    apply tendsto_const_nhds.congr'
    filter_upwards [hh] with n hn
    exact (levelCutoff_one g a (hε n) x (by linarith)).symm
  · rw [indicator_of_notMem (show x∉{y | g y<a} from hx)]
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n => (levelCutoff_zero g a (hε n) x (by have := hε n;linarith)).symm

theorem levelCutoff_hessian_identity (g u : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a})) {ε : ℝ} (hε : 0<ε) :
    (∫ x, levelCutoff g a ε x*((spatialLaplacian u x)^2-smoothHessianSq u x))=
      ∫ x, levelLayerWeight g a ε x*levelBoundaryFlux u g x :=
  weighted_level_hessian_identity _ _ _ _ (levelCutoff_contDiff g hg a ε)
    (levelCutoff_compact g hg.continuous a hK hε) hu (levelCutoff_fderiv g hg a ε)

theorem levelCutoff_gradient_mass (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (a : ℝ) (hK : IsCompact (closure {x | g x<a})) {ε : ℝ} (hε : 0<ε) :
    (∫ x, levelLayerWeight g a ε x*‖graphSlopeVector g x‖^2)=
      ∫ x, levelCutoff g a ε x*spatialLaplacian g x :=
  weighted_level_gradient_mass _ _ _ (levelCutoff_contDiff g hg a ε)
    (levelCutoff_compact g hg.continuous a hK hε) hg (levelCutoff_fderiv g hg a ε)

end Carleman
