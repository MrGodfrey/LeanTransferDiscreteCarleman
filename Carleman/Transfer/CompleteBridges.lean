module

public import Carleman.Transfer.CombinedErrors
public import Carleman.Transfer.Conditional
public import Carleman.Continuous.VariablePeriodicExistence

/-! Assemble all actual transfer bridges from continuous Carleman, original
numerical norm bounds, and the proved combined error theorem. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {α : CarlemanExponents} (a : OriginalForm (m := α.m) hS hν)
  {X F Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  {Z : Fin α.m → Type*} [∀ j, NormedAddCommGroup (Z j)]
  [∀ j, InnerProductSpace ℝ (Z j)]
  (w : TimeWeight) (ρ : SpatialProfile ν)
  (P : ∀ j : Fin α.m, DifferentialExpression ν
      (fun k : Fin (α.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
  (hstate : ∀ t v, state t v = 0 → v = 0)
  (hload : ∀ t v, load t v = 0 → v = 0)
  (hcontrol : ∀ t v, control t v = 0 → v = 0)

local notation "p" => sobolevGeometry hS hν a.sobolev w ρ P obs hobs state load control hstate hload hcontrol

variable {g : TimeGrid} {β : ℝ} (hq : TimeWeightRegularity w g β)
  (hD : a.model.domain ≤ sobolevSubspace d (2*α.m) ν S)
  (Creg : ℝ) (hell : ∀ v : a.model.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖a.model.operator v‖)
  (r : Reconstruction a.V X) (l : LoadInterface r F) (A : X →ₗ[ℝ] X)
  (Bstar : X →ₗ[ℝ] Y) (L τStar Kc K Cnum Cce : ℝ) (errors : ErrorScales)

include hq hD Creg hell in
/-- All B1/B3/B4 fields are constructed from actual equations and norms.
The final uniform theorem supplies the combined estimates internally. -/
theorem sobolevGeometry_transferBridges
    (hL : 1 ≤ L) (hmesh : g.dt*w.max^2 ≤ cellThreshold β α.comparisonExponent ρ.bound)
    (hCn : 0 ≤ Cnum) (hKc : 0 ≤ Kc) (hK9 : 9 ≤ K) (hKn : 9*Cnum ≤ K)
    (hKD : differentialFamilyBound P ≤ K) (hKL : (2*L)^(4*α.m) ≤ K)
    (hKcK : Kc^2 ≤ K) (hKce : Cce ≤ K)
    (hcover : max (α.dStar/2) (α.bStar/2) ≤ τStar)
    (hR : ∀ i v, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (r.RH v))^2 ≤
      Cnum*(state (g.nodeTime i) v)^2)
    (hnode : ∀ i v, (state (g.nodeTime i) v)^2 ≤
      Cnum*((ρ.multiplier w 0 (g.nodeTime i)).seminorm (r.RH v))^2)
    (hlift : ∀ i v, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (l.lift v))^2 ≤
      Cnum*(load (g.nodeTime i) v)^2)
    (hobsbound : ∀ i v, ((ρ.multiplier w 0 (g.nodeTime i)).observation obs hobs (r.RH v))^2 ≤
      Cnum*(control (g.nodeTime i) (Bstar v))^2)
    (hCE : ∀ (s : Orientation) (u : PeriodicWeakTrajectory g a.model.domain a.model.operator),
      (p).continuousEnergy g ((p).trajectory g a.domain_le u) ≤ Cce *
        (timeSq g w.q 0 (p).space (fun t => s.sign • u.derivative t+a.model.operator (u.domainValue t))+
         timeSq g w.q α.o (p).observation (fun t => (u.domainValue t : Lp ℝ 2 ν))))
    (hc : ∀ s τ, |τ| ≤ τStar → Section4.CombinedEstimate a r g s A ρ w L τ
      errors.aE errors.a₀ errors.ηA Kc) :
    TransferBridges (p) g r l a.model.operator A a.domain_le Bstar errors K τStar L := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hCnK : Cnum ≤ K := by nlinarith
  have hb := hq.mesh_bounds α.comparisonExponent ρ.bound
    α.comparisonExponent_bounds.1 ρ.bound_nonneg hmesh
  refine {
    shift_lower := hL
    shift_bound := ?_
    coverage := hcover
    reconstruction_bound := fun i v => (hR i v).trans
      (mul_le_mul_of_nonneg_right hCnK (sq_nonneg _))
    lift_bound := fun i v => (hlift i v).trans
      (mul_le_mul_of_nonneg_right hCnK (sq_nonneg _))
    solutions := ?_ }
  · have hh : L^(4*α.m) ≤ (2*L)^(4*α.m) := by gcongr; linarith
    exact hh.trans hKL
  · intro s f z _hz
    let μ := frozenShift α w g L
    let F := l.transferLoad g μ f z
    have hμ : ∀ᵐ t ∂g.timeMeasure, 0 ≤ (s.frozenMultiplier g μ).value t :=
      Filter.Eventually.of_forall fun t => by
        change 0 ≤ s.extension g μ t
        cases s <;> exact (frozenShift_pos α w g hL _).le
    obtain ⟨U,hU,_⟩ := a.model.existsUnique_variable_periodic g s
      (s.frozenMultiplier g μ) hμ (s.extensionLp g F)
    have hfrozen : ∀ᵐ t ∂g.timeMeasure,
      s.sign • U.toTrajectory.derivative t+a.model.operator (U.toTrajectory.domainValue t)+
        s.extension g μ t • U.toTrajectory.value t = s.extension g F t := by
      have he := (a.model.evolution_eq_iff g s (s.frozenMultiplier g μ) U (s.extensionLp g F)).mp hU
      filter_upwards [he,s.extensionLp_ae g F] with t ht hf
      exact ht.trans hf
    refine ⟨U.toTrajectory,?_,?_⟩
    · apply sobolevGeometry_comparisonBridge hS hν a.sobolev w ρ P obs hobs state load control
        hstate hload hcontrol hq a.domain_le hD Creg hell r l Bstar s μ f z U.toTrajectory
        hmesh Cnum Cnum Cnum K hCn hK9 hKn hKn hKn
        (fun i => hnode i (z i)) (fun i => hlift i (f i)) (fun i => hobsbound i (z i)) hfrozen
      exact (hCE s U.toTrajectory).trans (mul_le_mul_of_nonneg_right hKce
        (add_nonneg (timeSq_nonneg g w.q w.nonneg _ _ _) (timeSq_nonneg g w.q w.nonneg _ _ _)))
    · exact sobolevGeometry_errorBridge_of_combined hS hν a w ρ P obs hobs state load control
        hstate hload hcontrol hq hD Creg hell r l A s f z U L τStar Kc K errors hL0 hb.1 hKc
        hKD hKL hKcK (hc s) hU

end Carleman
