module

public import Carleman.Transfer.CombinedNorms

/-! Fill the substantive B4 fields from Theorem 4.2, for the exact Section 5
load and every one of its required weights. -/
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
  (s : Orientation) (f : g.Sequence F) (z : g.Sequence X) (U : a.model.PeriodicGraph g)
  (L τStar Kc K : ℝ) (errors : ErrorScales)

include hq hD Creg hell in
/-- This is a constructor, not an additional error hypothesis in the final
transfer: its combined estimates are supplied by the uniform Section 4 theorem. -/
theorem sobolevGeometry_errorBridge_of_combined
    (hL : 0 ≤ L) (hm : β*g.dt*w.max^2 ≤ 1/2) (hKc : 0 ≤ Kc)
    (hKD : differentialFamilyBound P ≤ K) (hKL : (2*L)^(4*α.m) ≤ K) (hKcK : Kc^2 ≤ K)
    (hc : ∀ τ, |τ| ≤ τStar → Section4.CombinedEstimate a r g s A ρ w L τ
      errors.aE errors.a₀ errors.ηA Kc)
    (hU : a.model.evolution g s (s.frozenMultiplier g (frozenShift α w g L)) U =
      s.extensionLp g (l.transferLoad g (frozenShift α w g L) f z)) :
    ErrorBridge (p) g r l a.model.operator A a.domain_le s (frozenShift α w g L)
      f z U.toTrajectory errors K τStar := by
  have haE := errors.aE_nonneg
  have ha0 := errors.a₀_nonneg
  have hη := errors.ηA_nonneg
  have hdt := g.dt_pos.le
  apply sobolevGeometry_errorBridge hS hν a.sobolev w ρ P obs hobs state load control
    hstate hload hcontrol hq a.domain_le hD Creg hell r l s f z U.toTrajectory A L hL hm
    errors K τStar hKD hKL
  · intro hz j hj
    let b := α.energyPower j
    have hb : 0 ≤ b := α.energyPower_nonneg j
    have hτ : |b/2| ≤ τStar := by rw [abs_of_nonneg (by positivity)]; exact hj
    have hz' : ∀ i, s.difference g z i+A (z i)+(L*w.nodes g i)^(2*α.m) • r.G (z i) =
        r.J (l.transferLoad g (frozenShift α w g L) f z i) := by
      intro i
      have hh := congrArg (fun v => v i) hz
      change s.difference g z i+(A (z i)+(L*w.nodes g i)^(2*α.m) • r.G (z i)) = r.J (l.transferLoad g (frozenShift α w g L) f z i) at hh
      simpa only [add_assoc] using hh
    obtain ⟨_,hJ,hE⟩ := hc (b/2) hτ _ z U hz' hU
    have hfn := g.l2Norm_nonneg (ρ.nodeMap g w (b/2) (l.transferLoad g (frozenShift α w g L) f z))
    have hs := (sq_le_sq₀ (WeakSobolevJet.spacetimeWeightedNorm_nonneg _ _ _ _)
      (by positivity : 0 ≤ Kc*(Real.sqrt g.dt+errors.aE+errors.ηA)*
        g.l2Norm (ρ.nodeMap g w (b/2) (l.transferLoad g (frozenShift α w g L) f z)))).mpr hE
    change (p).graphSq g b (Section4.reconstructedError a r g s U z) ≤ _
    rw [sobolevGeometry_graphSq_eq hS hν a.sobolev w ρ P obs hobs state load control
      hstate hload hcontrol hq.aestronglyMeasurable b hJ]
    have hF := g.powerSq_nonneg (w.nodes g) (fun i => w.nonneg _) b
      (fun i => (ρ.multiplier w 0 (g.nodeTime i)).seminorm)
      (l.transferLoad g (frozenShift α w g L) f z)
    have he : Real.sqrt g.dt+errors.aE+errors.ηA = errors.energy g := by
      dsimp [ErrorScales.energy]; ring
    rw [mul_pow,mul_pow,he,ρ.nodeMap_l2Norm_sq_powerSq] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKcK (sq_nonneg _)) hF)
  · intro hz b hb hτ
    have hb0 : 0 ≤ b := by
      rcases hb with rfl | rfl | rfl
      · exact α.c₀_pos.le
      · exact α.o_nonneg
      · positivity
    have hτ' : |b/2| ≤ τStar := by rw [abs_of_nonneg (by positivity)]; exact hτ
    have hz' : ∀ i, s.difference g z i+A (z i)+(L*w.nodes g i)^(2*α.m) • r.G (z i) =
        r.J (l.transferLoad g (frozenShift α w g L) f z i) := by
      intro i
      have hh := congrArg (fun v => v i) hz
      change s.difference g z i+(A (z i)+(L*w.nodes g i)^(2*α.m) • r.G (z i)) = r.J (l.transferLoad g (frozenShift α w g L) f z i) at hh
      simpa only [add_assoc] using hh
    obtain ⟨h0,hJ,_⟩ := hc (b/2) hτ' _ z U hz' hU
    have hvalue := conforming_value_L2 hS hν a.sobolev hJ
    change timeSq g w.q b (fun t => (ρ.multiplier w 0 t).seminorm)
      (fun t => (Section4.reconstructedError a r g s U z t : Lp ℝ 2 ν)) ≤ _
    rw [ρ.timeSq_eq_bochnerL2Norm_sq g w b hq.aestronglyMeasurable hvalue]
    have heq := bochnerL2Norm_congr_ae
      ((Section4.reconstructedError_value_ae a r g s U z).mono fun t ht =>
        congrArg ((ρ.multiplier w (b/2) t).map) ht)
    rw [heq]
    have hfn := g.l2Norm_nonneg (ρ.nodeMap g w (b/2) (l.transferLoad g (frozenShift α w g L) f z))
    have hs := (sq_le_sq₀ (bochnerL2Norm_nonneg _)
      (by positivity : 0 ≤ Kc*(g.dt+errors.a₀+errors.aE^2+errors.ηA)*
        g.l2Norm (ρ.nodeMap g w (b/2) (l.transferLoad g (frozenShift α w g L) f z)))).mpr h0
    have he : g.dt+errors.a₀+errors.aE^2+errors.ηA = errors.l2 g := by
      dsimp [ErrorScales.l2]; ring
    rw [mul_pow,mul_pow,he,ρ.nodeMap_l2Norm_sq_powerSq] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKcK (sq_nonneg _))
      (g.powerSq_nonneg _ (fun i => w.nonneg _) _ _ _))

end Carleman
