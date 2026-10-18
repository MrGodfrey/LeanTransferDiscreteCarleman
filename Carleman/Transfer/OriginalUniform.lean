module

public import Carleman.Transfer.OriginalData

/-! Original Theorem 2.1: constants precede every grid, numerical space,
allowed weight, full state and load. The combined error theorem is internal. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set
universe u v y
namespace Carleman.Section5
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  {α : CarlemanExponents} (a : OriginalForm (m := α.m) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d (2*α.m) ν S)
  (ρ : SpatialProfile ν)
  {Z : Fin α.m → Type*} [∀ j, NormedAddCommGroup (Z j)]
  [∀ j, InnerProductSpace ℝ (Z j)]
  (P : ∀ j : Fin α.m, DifferentialExpression ν
      (fun k : Fin (α.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (c C Ccomm β τStar Ctime Csuper δnum Cnum Cce : ℝ)

/-- Original A4 and N1--N5 are the only remaining analytic/numerical inputs.
Neither TransferBridges nor any error, graph or solution estimate is an input. -/
def TransferUniform : Prop :=
  ∃ δx δt ηstar cStar Cfinal : ℝ,
    0 < δx ∧ δx ≤ δnum ∧ 0 < δt ∧ 0 < ηstar ∧ 0 < cStar ∧ 0 < Cfinal ∧
    ∀ (X : Type u) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      (F : Type v) [AddCommGroup F] [Module ℝ F]
      (Y : Type y) [AddCommGroup Y] [Module ℝ Y]
      (r : Reconstruction a.V X) (A : X →ₗ[ℝ] X) (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
      (l : LoadInterface r F) (Bstar : X →ₗ[ℝ] Y)
      (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
      (hstate : ∀ t z, state t z = 0 → z = 0)
      (hload : ∀ t z, load t z = 0 → z = 0)
      (hcontrol : ∀ t z, control t z = 0 → z = 0)
      (g : TimeGrid) (w : TimeWeight), TimeWeightRegularity w g β →
      g.dt*w.max^2 ≤ δt →
      Section3.AllowedFamily hS hν a.sobolev hD a.scalarForm a.model.operator ρ w c C Ccomm τStar →
      ∀ (mesh : ℝ) (errors : ErrorScales), 0 ≤ mesh → mesh*w.max ≤ δx →
      errors.aE ≤ 1 → errors.ηA ≤ ηstar →
      NumericalData a hD r A b l Bstar g w ρ obs hobs state load control
        τStar Ctime Csuper Cnum mesh errors →
      let p := sobolevGeometry hS hν a.sobolev w ρ P obs hobs state load control hstate hload hcontrol
      (∀ (s : Orientation) (U : PeriodicWeakTrajectory g a.model.domain a.model.operator),
        p.continuousEnergy g (p.trajectory g a.domain_le U) ≤ Cce *
          (timeSq g w.q 0 p.space (fun t => s.sign • U.derivative t+a.model.operator (U.domainValue t))+
           timeSq g w.q α.o p.observation (fun t => (U.domainValue t : Lp ℝ 2 ν)))) →
      errors.loadDefect g α w.max ≤ 1 → errors.stateDefect g α w.max ≤ cStar →
      (∀ (s : Orientation) (f : g.Sequence F) (z : g.Sequence X),
        s.difference g z+g.map A z = (fun i => l.Γ (f i)) →
        p.nodeEnergy g r z ≤ Cfinal*(p.loadSq g f+p.observationSq g Bstar z)) ∧
      (∀ (I : X → F), (∀ z, l.Γ (I z) = z) →
        (∀ i z, (load (g.nodeTime i) (I z))^2 ≤ Cnum*(state (g.nodeTime i) z)^2) →
        ∀ (s : Orientation) (z : g.Sequence X),
        p.nodeEnergy g r z ≤ Cfinal*
          (g.weightedSq (p.node g p.state) (s.difference g z+g.map A z)+p.observationSq g Bstar z))

/-- Fixed-version bridge construction eliminates every conditional transfer
hypothesis once the actual Section 4 uniform theorem has been proved. -/
theorem transfer_uniform_of_combined [SFinite ν]
    (hβ : 0 < β) (hCn : 0 ≤ Cnum) (hCce : 0 ≤ Cce)
    (hcover : max (α.dStar/2) (α.bStar/2) ≤ τStar)
    (Creg : ℝ) (hell : ∀ v : a.model.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖a.model.operator v‖)
    (hcombined : Section4.CombinedUniform.{u} a hD ρ c C Ccomm β τStar Ctime Csuper δnum) :
    TransferUniform.{u,v,y} a hD ρ P obs hobs c C Ccomm β τStar Ctime Csuper δnum Cnum Cce := by
  obtain ⟨L,δtime,hL,hδtime,hcomb⟩ := hcombined
  obtain ⟨δx,ηstar,Kc,hδx,hδxnum,hηstar,hKc,hestimate⟩ := hcomb L le_rfl
  let K := 9+9*Cnum+Kc^2+(2*L)^(4*α.m)+differentialFamilyBound P+Cce
  have hD0 : 0 ≤ differentialFamilyBound P := zero_le_one.trans (differentialFamilyBound_ge_one P)
  have hpow : 0 ≤ (2*L)^(4*α.m) := pow_nonneg (by linarith) _
  have hK9 : 9 ≤ K := by dsimp [K]; nlinarith [sq_nonneg Kc]
  have hK1 : 1 ≤ K := by linarith
  have hKn : 9*Cnum ≤ K := by dsimp [K]; nlinarith [sq_nonneg Kc]
  have hKD : differentialFamilyBound P ≤ K := by dsimp [K]; nlinarith [sq_nonneg Kc]
  have hKL : (2*L)^(4*α.m) ≤ K := by dsimp [K]; nlinarith [sq_nonneg Kc]
  have hKcK : Kc^2 ≤ K := by dsimp [K]; nlinarith
  have hKce : Cce ≤ K := by dsimp [K]; nlinarith [sq_nonneg Kc]
  have hCnK : Cnum ≤ K := by nlinarith
  have htc := transferConstant_pos α hK1
  let δcell := cellThreshold β α.comparisonExponent ρ.bound
  have hδcell : 0 < δcell := cellThreshold_pos hβ α.comparisonExponent_bounds.1 ρ.bound_nonneg
  refine ⟨δx,min δtime δcell,ηstar,1/(2*transferConstant α K),4*transferConstant α K*K,
    hδx,hδxnum,lt_min hδtime hδcell,hηstar,by positivity,by positivity,?_⟩
  intro X _ _ F _ _ Y _ _ r A b l Bstar state load control hstate hload hcontrol
    g w hw hmesh ha mesh errors hx hxδ haE hη N p hCE hf hs
  have hcombined' (s : Orientation) (τ : ℝ) (hτ : |τ| ≤ τStar) :
      Section4.CombinedEstimate a r g s A ρ w L τ errors.aE errors.a₀ errors.ηA Kc := by
    have hinv : Section4.WeightedApproximation hS hν a.sobolev hD a.domain_le r g
        (ρ.signed false).neg w (-τ) errors.aE errors.a₀ := by
      rw [SpatialProfile.signed_neg]
      exact N.approximation true (-τ) (by simpa only [abs_neg] using hτ)
    exact hestimate X r A b N.stiffness g s w hw (hmesh.trans (min_le_left _ _))
      τ false hτ ha mesh errors.aE errors.a₀ errors.ηA hx hxδ errors.aE_nonneg haE
      errors.a₀_nonneg errors.ηA_nonneg hη (N.approximation false τ hτ) hinv (N.test false τ hτ)
      (N.defect false τ hτ)
  have bridge := sobolevGeometry_transferBridges hS hν a w ρ P obs hobs state load control
    hstate hload hcontrol hw hD Creg hell r l A Bstar L τStar Kc K Cnum Cce errors
    hL (hmesh.trans (min_le_right _ _)) hCn hKc.le hK9 hKn hKD hKL hKcK hKce hcover
    N.reconstruction_upper N.reconstruction_lower N.lift_bound N.observation_bound hCE hcombined'
  constructor
  · intro s f z hz
    have hh := bridge.load_estimate hK1 hf hs s f z hz
    have hF := g.weightedSq_nonneg (p.node g p.load) f
    have hO := g.powerSq_nonneg (w.nodes g) (fun _ => w.nonneg _) α.o
      (p.node g p.control) (fun i => Bstar (z i))
    exact hh.trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity : 0 ≤ 4*transferConstant α K) hK1)
      (add_nonneg hF hO))
  · intro I hI hInorm s z
    exact bridge.residual_estimate hK1 hf hs I hI
      (fun i v => (hInorm i v).trans (mul_le_mul_of_nonneg_right hCnK (sq_nonneg _))) s z

end Carleman.Section5

namespace Carleman.OriginalForm
variable {d : ℕ} {S : Set (SpatialCoordinates d)} {α : CarlemanExponents}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (hΩ : IsBoundedLipschitzDomain S E)
  (a : OriginalForm (m := α.m) (ν := volume.restrict S) hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet))
  (hD : a.model.domain ≤ sobolevSubspace d (2*α.m) (volume.restrict S) S)
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)
  {Z : Fin α.m → Type*} [∀ j, NormedAddCommGroup (Z j)] [∀ j, InnerProductSpace ℝ (Z j)]
  (P : ∀ j : Fin α.m, DifferentialExpression (volume.restrict S)
      (fun k : Fin (α.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)

include hρ in
/-- Theorem 2.1 from the original assumptions, with no remaining transfer
bridges. Both load and right-inverse residual estimates hold for every state. -/
theorem transfer_uniform (Creg c C Ccomm β τStar Ctime Csuper δnum Cnum Cce : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hCc : 0 ≤ Ccomm) (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδ : 0 < δnum) (hCn : 0 ≤ Cnum) (hCce : 0 ≤ Cce)
    (hcover : max (α.dStar/2) (α.bStar/2) ≤ τStar)
    (hell : ∀ v : a.model.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖a.model.operator v‖) :
    Section5.TransferUniform.{u,v,y} a hD ρ P obs hobs c C Ccomm β τStar Ctime Csuper δnum Cnum Cce := by
  exact Section5.transfer_uniform_of_combined a hD ρ P obs hobs c C Ccomm β τStar Ctime Csuper δnum Cnum Cce
    hβ hCn hCce hcover Creg hell
    (a.combined_uniform hΩ hD ρ hρ α.m_pos Creg c C Ccomm β τStar Ctime Csuper δnum
      hc hC hCc hβ hτ hCt hCs hδ hell)

end Carleman.OriginalForm
