module

public import Carleman.Spatial.LevelDivergence
public import Carleman.Spatial.LevelHeatBoundary
public import Carleman.Spatial.BoxIntegratedHeatIdentity
public import Carleman.Spatial.PeriodicHeatFlux

/-! Actual space-time integration on bounded domains and the heat Carleman
inequality on the genuine curved smooth inner domains. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

def domainTimeIntegral (S : Set (SpatialCoordinates d)) (T : ℝ)
    (f : (ℝ × SpatialCoordinates d) → ℝ) : ℝ :=
  ∫ tx, f tx ∂((volume.restrict (Icc 0 T)).prod (volume.restrict S))

theorem continuous_domain_time_integrable (S : Set (SpatialCoordinates d)) (hb : Bornology.IsBounded S) (T : ℝ)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) :
    Integrable f ((volume.restrict (Icc 0 T)).prod (volume.restrict S)) := by
  have hk : IsCompact ((Icc (0:ℝ) T) ×ˢ closure S) :=
    isCompact_Icc.prod hb.isCompact_closure
  have hi := ContinuousOn.integrableOn_compact (μ := volume) hk hf.continuousOn
  rw [Measure.prod_restrict]
  exact hi.mono_set (prod_mono subset_rfl subset_closure)

theorem domainTimeIntegral_eq_iterated (S : Set (SpatialCoordinates d)) (hb : Bornology.IsBounded S) (T : ℝ)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) :
    domainTimeIntegral S T f = ∫ t in Icc 0 T, ∫ x in S, f (t,x) :=
  integral_prod f (continuous_domain_time_integrable S hb T hf)

theorem domainTimeIntegral_add (S : Set (SpatialCoordinates d)) (hb : Bornology.IsBounded S) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    domainTimeIntegral S T (fun x => f x+g x)=domainTimeIntegral S T f+domainTimeIntegral S T g :=
  integral_add (continuous_domain_time_integrable S hb T hf) (continuous_domain_time_integrable S hb T hg)

theorem domainTimeIntegral_mono (S : Set (SpatialCoordinates d)) (hb : Bornology.IsBounded S) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x ≤ g x) : domainTimeIntegral S T f ≤ domainTimeIntegral S T g :=
  integral_mono (continuous_domain_time_integrable S hb T hf) (continuous_domain_time_integrable S hb T hg) hfg

theorem domainTimeIntegral_nonpos_of_spatial (S : Set (SpatialCoordinates d)) (hb : Bornology.IsBounded S) (T : ℝ)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f)
    (hs : ∀ t ∈ Icc 0 T, (∫ x in S, f (t,x)) ≤ 0) :
    domainTimeIntegral S T f ≤ 0 := by
  rw [domainTimeIntegral_eq_iterated S hb T hf]
  exact setIntegral_nonpos measurableSet_Icc hs

theorem domainTimeIntegral_periodic_derivative (S : Set (SpatialCoordinates d)) (hb : Bornology.IsBounded S) {T : ℝ} (hT : 0 ≤ T)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (T,0)) :
    domainTimeIntegral S T (smoothD (1,0) f)=0 := by
  unfold domainTimeIntegral
  rw [integral_prod_symm _ (continuous_domain_time_integrable S hb T
    (smoothD_contDiff hf (1,0)).continuous)]
  have he (x : SpatialCoordinates d) : (∫ t in Icc 0 T, smoothD (1,0) f (t,x))=0 := by
    rw [← setIntegral_congr_set (Ioc_ae_eq_Icc : Ioc (0:ℝ) T =ᵐ[volume] Icc 0 T),
      ← intervalIntegral.integral_of_le hT]
    exact spacetime_periodic_derivative_integral hf T hp x
  simp only [he,integral_zero]


theorem halfspaceSmoothInner_heat_flux_integral {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) (n : ℕ)
    (c : SpatialCoordinates d) (hc : c ∈ halfspaceSmoothInner ℓ b n)
    {l : ℝ} (hl : 0 ≤ l) {q : ℝ → ℝ}
    {L u k p : (ℝ × SpatialCoordinates d) → ℝ}
    (hL : ContDiff ℝ ∞ L) (hu : ContDiff ℝ ∞ u)
    (hk : ContDiff ℝ ∞ k) (hp : ContDiff ℝ ∞ p)
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (hboundary : ∀ s y, y ∈ frontier (halfspaceSmoothInner ℓ b n) → u (s,y)=0)
    (t : ℝ) (hq : 0 ≤ q t) :
    let z := fun y => Real.exp (L y)*u y
    (∫ x in halfspaceSmoothInner ℓ b n, ∑ i,
      smoothD (spaceTimeSpatialDirection i)
        (pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i) (t,x)) ≤ 0 := by
  let z := fun y => Real.exp (L y)*u y
  let F := fun i y => pointwiseHeatFlux spaceTimeSpatialDirection (1,0) L k p z i (t,y)
  have hz : ContDiff ℝ ∞ z := hL.exp.mul hu
  have hF (i : Fin d) : ContDiff ℝ ∞ (F i) :=
    (pointwiseHeatFlux_contDiff _ _ hL hk hp hz i).comp (contDiff_const.prodMk contDiff_id)
  have hi := level_divergence_nonpos (halfspaceExpSum ℓ b n) F
    (halfspaceExpSum_contDiff ℓ b n) hF (1/2) (halfspaceSmoothInner_compact ℓ b hb n)
    (fun x hx => (halfspaceSmoothInner_boundary_regular ℓ b n hc hx).2)
    (fun x hx => halfspaceSmoothInner_gaussian_heat_flux_nonpos ℓ b n c hc hl hL hu
      hformula hboundary k p t hq x hx)
  convert hi using 1
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro i _
  exact spaceTime_spatialD (pointwiseHeatFlux_contDiff _ _ hL hk hp hz i)
    t x (EuclideanSpace.basisFun (Fin d) ℝ i)

theorem halfspaceSmoothInner_smooth_heat_carleman_inequality {ι : Type*} [Fintype ι]
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x}) (n : ℕ)
    (c : SpatialCoordinates d) (hc : c ∈ halfspaceSmoothInner ℓ b n)
    {T l : ℝ} (hT : 0 ≤ T) (hl : 0 ≤ l) {q : ℝ → ℝ}
    {L p u : (ℝ × SpatialCoordinates d) → ℝ}
    (hL : ContDiff ℝ ∞ L) (hp : ContDiff ℝ ∞ p) (hu : ContDiff ℝ ∞ u)
    (hpl : Function.Periodic L (T,0)) (hpp : Function.Periodic p (T,0))
    (hpu : Function.Periodic u (T,0))
    (hformula : ∀ s y, L (s,y)=q s*interiorCarlemanProfile c l y)
    (hboundary : ∀ s : ℝ, ∀ y ∈ frontier (halfspaceSmoothInner ℓ b n), u (s,y)=0)
    (hq : ∀ t ∈ Icc 0 T, 0 ≤ q t) :
    let e := spaceTimeSpatialDirection (d := d)
    let z := fun y => Real.exp (L y)*u y
    let k := heatConjugationK e (1,0) L p
    domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (heatCarlemanBulk e (1,0) L k p z) ≤
      domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun y => (Real.exp (L y)*spaceTimeHeat u y)^2) := by
  have hb := (halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure
  let e := spaceTimeSpatialDirection (d := d)
  let z := fun y => Real.exp (L y)*u y
  let k := heatConjugationK e (1,0) L p
  let R := fun y => (Real.exp (L y)*spaceTimeHeat u y)^2
  let M := smoothD (1,0) (pointwiseHeatTimeFlux e k z)
  let V := fun x => ∑ i, smoothD (e i) (pointwiseHeatFlux e (1,0) L k p z i) x
  have hz : ContDiff ℝ ∞ z := hL.exp.mul hu
  have hk : ContDiff ℝ ∞ k := heatConjugationK_contDiff e (1,0) hL hp
  have hR : ContDiff ℝ ∞ R := (hL.exp.mul (spaceTimeHeat_contDiff hu)).pow 2
  have hM : ContDiff ℝ ∞ M :=
    smoothD_contDiff (pointwiseHeatTimeFlux_contDiff e hk hz) (1,0)
  have hV : ContDiff ℝ ∞ V := pointwiseHeatDivergence_contDiff e (1,0) hL hk hp hz
  have hzero : domainTimeIntegral (halfspaceSmoothInner ℓ b n) T M=0 := by
    apply domainTimeIntegral_periodic_derivative _ hb hT (pointwiseHeatTimeFlux_contDiff e hk hz)
    exact pointwiseHeatTimeFlux_periodic e (heatConjugationK_periodic e (1,0) hpl hpp)
      ((hpl.comp Real.exp).mul hpu)
  have hnonpos : domainTimeIntegral (halfspaceSmoothInner ℓ b n) T V ≤ 0 := by
    apply domainTimeIntegral_nonpos_of_spatial _ hb T hV.continuous
    intro t ht
    exact halfspaceSmoothInner_heat_flux_integral ℓ b hbounded n c hc hl hL hu hk hp hformula hboundary t (hq t ht)
  have hi : domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (heatCarlemanBulk e (1,0) L k p z) ≤
      domainTimeIntegral (halfspaceSmoothInner ℓ b n) T (fun y => R y+M y+V y) :=
    domainTimeIntegral_mono _ hb T (heatCarlemanBulk_contDiff e (1,0) hL hk hp hz).continuous
      ((hR.add hM).add hV).continuous (fun y => spacetime_heat_carleman_inequality hL hp hu y)
  rw [domainTimeIntegral_add _ hb T (hR.add hM).continuous hV.continuous,
    domainTimeIntegral_add _ hb T hR.continuous hM.continuous,hzero,add_zero] at hi
  exact hi.trans (add_le_of_nonpos_right hnonpos)


end Carleman
