module

public import Carleman.Transfer.OriginalUniform
public import Carleman.Transfer.ScaleSmallness

/-! Original Corollaries 2.2 and 2.3, including both full estimates.
All thresholds precede the numerical spaces, time grid, weight and states. -/
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

def ScaleUniform (Cap xrate trate : ℝ) : Prop :=
  ∃ κ h0 Δ0 Cfinal : ℝ,
    0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < Cfinal ∧
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
      Section3.AllowedFamily hS hν a.sobolev hD a.scalarForm a.model.operator ρ w c C Ccomm τStar →
      ∀ (mesh : ℝ) (errors : ErrorScales), 0 < mesh → mesh ≤ h0 → g.dt ≤ Δ0 →
      w.max ≤ κ*min (mesh^(-xrate)) (g.dt^(-trate)) →
      errors.aE ≤ Cap*mesh^α.m → errors.a₀+errors.ηA ≤ Cap*mesh^(2*α.m) →
      NumericalData a hD r A b l Bstar g w ρ obs hobs state load control
        τStar Ctime Csuper Cnum mesh errors →
      let p := sobolevGeometry hS hν a.sobolev w ρ P obs hobs state load control hstate hload hcontrol
      (∀ (s : Orientation) (U : PeriodicWeakTrajectory g a.model.domain a.model.operator),
        p.continuousEnergy g (p.trajectory g a.domain_le U) ≤ Cce *
          (timeSq g w.q 0 p.space (fun t => s.sign • U.derivative t+a.model.operator (U.domainValue t))+
           timeSq g w.q α.o p.observation (fun t => (U.domainValue t : Lp ℝ 2 ν)))) →
      (∀ (s : Orientation) (f : g.Sequence F) (z : g.Sequence X),
        s.difference g z+g.map A z = (fun i => l.Γ (f i)) →
        p.nodeEnergy g r z ≤ Cfinal*(p.loadSq g f+p.observationSq g Bstar z)) ∧
      (∀ (I : X → F), (∀ z, l.Γ (I z) = z) →
        (∀ i z, (load (g.nodeTime i) (I z))^2 ≤ Cnum*(state (g.nodeTime i) z)^2) →
        ∀ (s : Orientation) (z : g.Sequence X),
        p.nodeEnergy g r z ≤ Cfinal*
          (g.weightedSq (p.node g p.state) (s.difference g z+g.map A z)+p.observationSq g Bstar z))

/-- The scale hypotheses discharge all smallness requirements internally. -/
theorem scale_uniform_of_transfer (Cap : ℝ) (hCap : 0 ≤ Cap)
    (htransfer : TransferUniform.{u,v,y} a hD ρ P obs hobs c C Ccomm β τStar Ctime Csuper δnum Cnum Cce) :
    ScaleUniform.{u,v,y} a hD ρ P obs hobs c C Ccomm β τStar Ctime Csuper Cnum Cce Cap α.alphaX α.alphaT := by
  obtain ⟨δx,δt,ηstar,cStar,Cfinal,hδx,_hδnum,hδt,hη,hc,hCf,ht⟩ := htransfer
  obtain ⟨κ,h0,Δ0,hκ,hh0,hh01,hΔ0,hΔ01,hs⟩ := exists_scale_smallness α Cap δx δt ηstar cStar hCap hδx hδt hη hc
  refine ⟨κ,h0,Δ0,Cfinal,hκ,hh0,hh01,hΔ0,hΔ01,hCf,?_⟩
  intro X _ _ F _ _ Y _ _ r A b l Bstar state load control hstate hload hcontrol
    g w hw ha mesh errors hx hx0 hdt hscale haE ha0 N p hCE
  have hsmall := hs g mesh w.max errors hx hx0 hdt w.max_ge_one hscale haE ha0
  exact ht X F Y r A b l Bstar state load control hstate hload hcontrol g w hw
    hsmall.2.2.2.1 ha mesh errors hx.le hsmall.2.2.1 hsmall.1 hsmall.2.1 N hCE
    hsmall.2.2.2.2.1 hsmall.2.2.2.2.2

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
/-- Corollary 2.2 from the original assumptions and approximation orders.
Both load and right-inverse residual estimates hold for every state. -/
theorem scale_uniform (Cap Creg c C Ccomm β τStar Ctime Csuper δnum Cnum Cce : ℝ)
    (hCap : 0 ≤ Cap) (hc : 0 < c) (hC : 0 ≤ C) (hCc : 0 ≤ Ccomm) (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδ : 0 < δnum) (hCn : 0 ≤ Cnum) (hCce : 0 ≤ Cce)
    (hcover : max (α.dStar/2) (α.bStar/2) ≤ τStar)
    (hell : ∀ v : a.model.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖a.model.operator v‖) :
    Section5.ScaleUniform.{u,v,y} a hD ρ P obs hobs c C Ccomm β τStar Ctime Csuper Cnum Cce Cap α.alphaX α.alphaT := by
  exact Section5.scale_uniform_of_transfer a hD ρ P obs hobs c C Ccomm β τStar Ctime Csuper δnum Cnum Cce Cap hCap
    (a.transfer_uniform hΩ hD ρ hρ P obs hobs Creg c C Ccomm β τStar Ctime Csuper δnum Cnum Cce
      hc hC hCc hβ hτ hCt hCs hδ hCn hCce hcover hell)

end Carleman.OriginalForm
