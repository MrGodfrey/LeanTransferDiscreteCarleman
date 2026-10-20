module
public import Carleman.Geometry.SmoothLevelCutoff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-! Classical convex level-domain Hessian estimate, with an actual thin-layer limit. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem exists_positive_level_layer (g F : SpatialCoordinates d → ℝ)
    (hg : Continuous g) (hF : Continuous F) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a}))
    (hb : ∀ c ∈ frontier {x | g x<a}, 0<F c) :
    ∃ r : ℝ, 0<r ∧ ∀ x ∈ closure {y | g y<a}, a-2*r≤g x → 0<F x := by
  let K := closure {x | g x<a} ∩ {x | F x≤0}
  have hcK : IsCompact K := hK.of_isClosed_subset
    (isClosed_closure.inter (isClosed_le hF continuous_const)) inter_subset_left
  have hS : IsOpen {x | g x<a} := isOpen_lt hg continuous_const
  have hlt (x : SpatialCoordinates d) (hx : x∈K) : g x<a := by
    by_contra hn
    have hc : x∈frontier {y | g y<a} := by rw [hS.frontier_eq];exact ⟨hx.1,hn⟩
    have hh := hb x hc
    have hx' : F x≤0 := hx.2
    linarith
  by_cases hne : K.Nonempty
  · obtain ⟨c,hc,hmax⟩ := hcK.exists_isMaxOn hne hg.continuousOn
    refine ⟨(a-g c)/4,by have := hlt c hc;linarith,?_⟩
    intro x hx hl
    by_contra hn
    have hxK : x∈K := ⟨hx,le_of_not_gt hn⟩
    have hm : g x≤g c := hmax hxK
    have hh := hlt c hc
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro x hx _
    by_contra hn
    exact hne ⟨x,hx,le_of_not_gt hn⟩

theorem levelLayer_flux_lower_bound (g u : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a}))
    (hreg : ∀ c ∈ frontier {x | g x<a}, fderiv ℝ g c≠0)
    (hflux : ∀ c ∈ frontier {x | g x<a}, 0≤levelBoundaryFlux u g c)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ r : ℝ, 0<r ∧ ∀ ε : ℝ, 0<ε → ε≤r → ∀ x,
      -δ*(levelLayerWeight g a ε x*‖graphSlopeVector g x‖^2)≤
        levelLayerWeight g a ε x*levelBoundaryFlux u g x := by
  let F := fun x => levelBoundaryFlux u g x+δ*‖graphSlopeVector g x‖^2
  have hF : Continuous F := (levelBoundaryFlux_contDiff u g hu hg).continuous.add
    (continuous_const.mul (((graphSlopeVector_contDiff g hg).continuous.norm).pow 2))
  have hb : ∀ c ∈ frontier {x | g x<a}, 0<F c := by
    intro c hc
    have hp : 0<‖graphSlopeVector g c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (graphSlopeVector_ne_zero (hreg c hc)))
    exact add_pos_of_nonneg_of_pos (hflux c hc) (mul_pos hδ hp)
  obtain ⟨r,hr,hnear⟩ := exists_positive_level_layer g F hg.continuous hF a hK hb
  refine ⟨r,hr,?_⟩
  intro ε hε hεr x
  by_cases hw : levelLayerWeight g a ε x=0
  · simp [hw]
  · have hts : x∈tsupport (levelLayerWeight g a ε) := subset_closure hw
    obtain ⟨hl,hh⟩ := levelLayerWeight_tsupport g hg.continuous a hε hts
    have hxS : x∈{y | g y<a} := by change g x<a;linarith
    have hpos := hnear x (subset_closure hxS) (by linarith)
    have hh' : -δ*‖graphSlopeVector g x‖^2≤levelBoundaryFlux u g x := by change 0<_+_ at hpos;linarith
    have hmul := mul_le_mul_of_nonneg_left hh' (levelLayerWeight_nonneg g a hε x)
    nlinarith

theorem continuous_integrableOn_bounded_sublevel (g F : SpatialCoordinates d → ℝ)
    (hF : Continuous F) (a : ℝ) (hK : IsCompact (closure {x | g x<a})) :
    IntegrableOn F {x | g x<a} volume :=
  (ContinuousOn.integrableOn_compact hK hF.continuousOn).mono_set subset_closure

theorem levelCutoff_integral_tendsto (g F : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hF : Continuous F) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a})) (ε : ℕ → ℝ)
    (hε : ∀ n, 0<ε n) (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, levelCutoff g a (ε n) x*F x) atTop (𝓝 (∫ x in {x | g x<a}, F x)) := by
  let S := {x | g x<a}
  have hS : MeasurableSet S := (isOpen_lt hg.continuous continuous_const).measurableSet
  have hI : Integrable (S.indicator (fun x => |F x|)) volume :=
    (continuous_integrableOn_bounded_sublevel g _ hF.abs a hK).integrable_indicator hS
  rw [← integral_indicator hS]
  apply tendsto_integral_of_dominated_convergence (S.indicator (fun x => |F x|))
    (fun n => ((levelCutoff_contDiff g hg a (ε n)).continuous.mul hF).aestronglyMeasurable) hI
  · intro n
    refine Eventually.of_forall fun x => ?_
    change ‖levelCutoff g a (ε n) x*F x‖≤S.indicator (fun y => |F y|) x
    by_cases hx : x∈S
    · rw [indicator_of_mem hx]
      simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (levelCutoff_bounds g a (ε n) x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (levelCutoff_bounds g a (ε n) x).2
    · have hh : levelCutoff g a (ε n) x=0 := levelCutoff_zero g a (hε n) x (by
        have hh : ¬g x<a := hx
        have := hε n
        linarith)
      rw [indicator_of_notMem hx,hh,zero_mul,norm_zero]
  · refine Eventually.of_forall fun x => ?_
    have hh := (levelCutoff_tendsto g a ε hε ht x).mul_const (F x)
    convert hh using 1
    by_cases hx : g x<a
    · simp only [S,indicator_of_mem (show x∈{y | g y<a} from hx),one_mul]
    · simp only [S,indicator_of_notMem (show x∉{y | g y<a} from hx),zero_mul]

theorem levelCutoff_mass_bound (g : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (a : ℝ) (hK : IsCompact (closure {x | g x<a}))
    {ε : ℝ} (hε : 0<ε) :
    (∫ x, levelLayerWeight g a ε x*‖graphSlopeVector g x‖^2)≤
      ∫ x in {x | g x<a}, |spatialLaplacian g x| := by
  let S := {x | g x<a}
  have hS : MeasurableSet S := (isOpen_lt hg.continuous continuous_const).measurableSet
  have hI : Integrable (S.indicator (fun x => |spatialLaplacian g x|)) volume :=
    (continuous_integrableOn_bounded_sublevel g _ (spatialLaplacian_contDiff g hg).continuous.abs a hK).integrable_indicator hS
  rw [levelCutoff_gradient_mass g hg a hK hε,← integral_indicator hS]
  apply integral_mono (compact_smooth_product_integrable _ _ (levelCutoff_contDiff g hg a ε)
    (levelCutoff_compact g hg.continuous a hK hε) (spatialLaplacian_contDiff g hg)) hI
  intro x
  dsimp only
  by_cases hx : x∈S
  · rw [indicator_of_mem hx]
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) (levelCutoff_bounds g a ε x).1).trans
      (mul_le_of_le_one_left (abs_nonneg _) (levelCutoff_bounds g a ε x).2)
  · have hh : levelCutoff g a ε x=0 := levelCutoff_zero g a hε x (by
      have hh : ¬g x<a := hx
      linarith)
    rw [indicator_of_notMem hx,hh,zero_mul]

theorem levelCutoff_defect_lower_bound (g u : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a}))
    (hreg : ∀ c ∈ frontier {x | g x<a}, fderiv ℝ g c≠0)
    (hflux : ∀ c ∈ frontier {x | g x<a}, 0≤levelBoundaryFlux u g c)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ r : ℝ, 0<r ∧ ∀ ε : ℝ, 0<ε → ε≤r →
      -δ*(∫ x in {x | g x<a}, |spatialLaplacian g x|)≤
        ∫ x, levelCutoff g a ε x*((spatialLaplacian u x)^2-smoothHessianSq u x) := by
  obtain ⟨r,hr,hb⟩ := levelLayer_flux_lower_bound g u hg hu a hK hreg hflux hδ
  refine ⟨r,hr,?_⟩
  intro ε hε hεr
  have hm : Integrable (fun x => levelLayerWeight g a ε x*‖graphSlopeVector g x‖^2) volume :=
    ((levelLayerWeight_contDiff g hg a ε).continuous.mul
      (((graphSlopeVector_contDiff g hg).continuous.norm).pow 2)).integrable_of_hasCompactSupport
      (levelLayerWeight_compact g hg.continuous a hK hε).mul_right
  have hf := compact_smooth_product_integrable _ _ (levelLayerWeight_contDiff g hg a ε)
    (levelLayerWeight_compact g hg.continuous a hK hε) (levelBoundaryFlux_contDiff u g hu hg)
  have hi := integral_mono (hm.const_mul (-δ)) hf (hb ε hε hεr)
  rw [integral_const_mul] at hi
  have hmass := levelCutoff_mass_bound g hg a hK hε
  rw [levelCutoff_hessian_identity g u hg hu a hK hε]
  nlinarith

theorem classical_level_hessian_defect_nonneg (g u : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a}))
    (hreg : ∀ c ∈ frontier {x | g x<a}, fderiv ℝ g c≠0)
    (hflux : ∀ c ∈ frontier {x | g x<a}, 0≤levelBoundaryFlux u g c) :
    0≤∫ x in {x | g x<a}, (spatialLaplacian u x)^2-smoothHessianSq u x := by
  let ε := fun n : ℕ => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0<ε n := by dsimp [ε];positivity
  have ht : Tendsto ε atTop (𝓝 (0:ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  let L := ∫ x in {x | g x<a}, (spatialLaplacian u x)^2-smoothHessianSq u x
  let M := ∫ x in {x | g x<a}, |spatialLaplacian g x|
  have hlim : Tendsto (fun n => ∫ x, levelCutoff g a (ε n) x*((spatialLaplacian u x)^2-smoothHessianSq u x)) atTop (𝓝 L) :=
    levelCutoff_integral_tendsto g _ hg
      (((spatialLaplacian_contDiff u hu).pow 2).sub (smoothHessianSq_contDiff u hu)).continuous a hK ε hε ht
  have hb (δ : ℝ) (hδ : 0<δ) : -δ*M≤L := by
    obtain ⟨r,hr,hbound⟩ := levelCutoff_defect_lower_bound g u hg hu a hK hreg hflux hδ
    apply ge_of_tendsto hlim
    have he : ∀ᶠ n in atTop, ε n<r := ht.eventually (gt_mem_nhds hr)
    filter_upwards [he] with n hn
    exact hbound (ε n) (hε n) hn.le
  have ht' : Tendsto (fun n => -(ε n)*M) atTop (𝓝 (0:ℝ)) := by simpa using ht.neg.mul_const M
  exact le_of_tendsto ht' (Eventually.of_forall fun n => hb (ε n) (hε n))

theorem classical_level_hessian_le_laplacian (g u : SpatialCoordinates d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (a : ℝ)
    (hK : IsCompact (closure {x | g x<a}))
    (hreg : ∀ c ∈ frontier {x | g x<a}, fderiv ℝ g c≠0)
    (hflux : ∀ c ∈ frontier {x | g x<a}, 0≤levelBoundaryFlux u g c) :
    (∫ x in {x | g x<a}, smoothHessianSq u x)≤∫ x in {x | g x<a}, (spatialLaplacian u x)^2 := by
  have hi := classical_level_hessian_defect_nonneg g u hg hu a hK hreg hflux
  rw [integral_sub (continuous_integrableOn_bounded_sublevel g _ ((spatialLaplacian_contDiff u hu).pow 2).continuous a hK)
    (continuous_integrableOn_bounded_sublevel g _ (smoothHessianSq_contDiff u hu).continuous a hK)] at hi
  exact sub_nonneg.mp hi

theorem halfspaceSmoothInner_classical_hessian_bound {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) (n : ℕ)
    {z : SpatialCoordinates d} (hz : z∈halfspaceSmoothInner ℓ b n)
    (u : SpatialCoordinates d → ℝ) (hu : ContDiff ℝ ∞ u)
    (hzero : ∀ x∈frontier (halfspaceSmoothInner ℓ b n), u x=0) :
    (∫ x in halfspaceSmoothInner ℓ b n, smoothHessianSq u x)≤
      ∫ x in halfspaceSmoothInner ℓ b n, (spatialLaplacian u x)^2 :=
  classical_level_hessian_le_laplacian (halfspaceExpSum ℓ b n) u (halfspaceExpSum_contDiff ℓ b n) hu (1/2)
    (halfspaceSmoothInner_compact ℓ b hbounded n)
    (fun _c hc => (halfspaceSmoothInner_boundary_regular ℓ b n hz hc).2)
    (fun c hc => halfspaceSmoothInner_boundaryFlux_nonneg ℓ b n hz u hu hzero (c := c) hc)

end Carleman
