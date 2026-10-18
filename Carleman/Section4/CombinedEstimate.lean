module

public import Carleman.Section4.SpatialUniform
public import Carleman.Spatial.SpacetimeCellEnergy

/-! Theorem 4.2 on the actual frozen continuous and full discrete solutions.
The intermediary Euler solution is constructed, not supplied as a hypothesis. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman.Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (r : Reconstruction a.V X) (g : TimeGrid) (s : Orientation)

/-- An actual V-valued representative of the full reconstruction error. -/
def reconstructedError (p : a.model.PeriodicGraph g) (z : g.Sequence X) (t : ℝ) : a.V :=
  Submodule.inclusion a.domain_le (p.toTrajectory.domainValue t)-r.R (s.extension g z t)

theorem reconstructedError_value_ae (p : a.model.PeriodicGraph g) (z : g.Sequence X) :
    (fun t => (reconstructedError a r g s p z t : Lp ℝ 2 ν)) =ᵐ[g.timeMeasure]
      (fun t => p.toTrajectory.value t-r.RH (s.extension g z t)) := by
  filter_upwards [p.toTrajectory.domainValue_ae] with t ht
  change (p.toTrajectory.domainValue t : Lp ℝ 2 ν)-r.RH (s.extension g z t) = _
  rw [ht]

theorem reconstructedError_decomposition (p : a.model.PeriodicGraph g)
    (u : g.Sequence a.model.domain) (z : g.Sequence X) (t : ℝ) :
    reconstructedError a r g s p z t =
      Submodule.inclusion a.domain_le (p.toTrajectory.domainError s u t)+
        s.extension g (fun i => Submodule.inclusion a.domain_le (u i)-r.R (z i)) t := by
  simp only [reconstructedError,PeriodicWeakTrajectory.domainError,map_sub]
  cases s <;> dsimp only [Orientation.extension,TimeGrid.extensionPlus,TimeGrid.extensionMinus] <;> abel

variable (A : X →ₗ[ℝ] X) (ρ : SpatialProfile ν) (w : TimeWeight) (L τ aE a0 ηA K : ℝ)

/-- Full original space-time errors with actual weak derivatives and MemLp. -/
def CombinedEstimate : Prop :=
  ∀ (f : g.Sequence (Lp ℝ 2 ν)) (z : g.Sequence X) (p : a.model.PeriodicGraph g),
    (∀ i, s.difference g z i+A (z i)+(L*w.nodes g i)^(2*m) • r.G (z i) = r.J (f i)) →
    a.model.evolution g s (s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))) p = s.extensionLp g f →
    bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
      (p.toTrajectory.value t-r.RH (s.extension g z t))) ≤
        K*(g.dt+a0+aE^2+ηA)*g.l2Norm (ρ.nodeMap g w τ f) ∧
    MemLp (fun t => domainSobolevJet hS hν a.sobolev (reconstructedError a r g s p z t)) 2 g.timeMeasure ∧
    WeakSobolevJet.spacetimeWeightedNorm g w.q (ρ.multiplier w τ)
      (fun t => domainSobolevJet hS hν a.sobolev (reconstructedError a r g s p z t)) ≤
        K*(Real.sqrt g.dt+aE+ηA)*g.l2Norm (ρ.nodeMap g w τ f)

theorem combine_nonnegative_rates {c d x y F : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hx : 0 ≤ x) (hy : 0 ≤ y) (hF : 0 ≤ F) :
    c*x*F+d*y*F ≤ (c+d)*(x+y)*F := by
  have hh : c*x+d*y ≤ (c+d)*(x+y) := by
    nlinarith only [mul_nonneg hc hy,mul_nonneg hd hx]
  exact (by convert mul_le_mul_of_nonneg_right hh hF using 1; ring)

theorem combined_estimate_of_spatial_temporal [SFinite ν]
    (hD : a.model.domain ≤ sobolevSubspace d (2*m) ν S)
    {β τStar Kt Ks Kg aE a0 ηA : ℝ}
    (hw : TimeWeightRegularity w g β) (hτStar : 0 ≤ τStar) (hτ : |τ| ≤ τStar)
    (hmesh : g.dt*w.max^2 ≤ cellThreshold β (τStar+m) ρ.bound)
    (hKt : 0 ≤ Kt) (hKs : 0 ≤ Ks) (haE : 0 ≤ aE) (ha0 : 0 ≤ a0) (hη : 0 ≤ ηA)
    (hg : Section3.EulerEstimate hS hν a.model hD g s w ρ L τ Kg)
    (ht : Section3.TemporalEstimate hS hν a.model a.sobolev a.domain_le g s w ρ L τ Kt)
    (hE : EnergyEstimate a r A g s ρ w L τ aE ηA Ks)
    (h0 : L2Estimate a r A g s ρ w L τ aE a0 ηA Ks) :
    CombinedEstimate a r g s A ρ w L τ aE a0 ηA (Kt+3*Ks) := by
  intro f z p hz hp
  obtain ⟨u,hu,_⟩ := (hg f).1
  obtain ⟨ht0,hJ,htE⟩ := ht f u p hu hp
  have hsE := (hE f u z hu hz).1
  have hs0 := h0 f u z hu hz
  let es : g.Sequence a.V := fun i => Submodule.inclusion a.domain_le (u i)-r.R (z i)
  let Jt := fun t => domainSobolevJet hS hν a.sobolev
    (Submodule.inclusion a.domain_le (p.toTrajectory.domainError s u t))
  let Js := fun i => domainSobolevJet hS hν a.sobolev (es i)
  have heq : (fun t => domainSobolevJet hS hν a.sobolev (reconstructedError a r g s p z t)) =
      Jt+s.extension g Js := by
    funext t
    rw [reconstructedError_decomposition a r g s p u z t,map_add]
    cases s <;> rfl
  have hJs : MemLp (s.extension g Js) 2 g.timeMeasure := s.memLp_extension g Js
  have hfT (k : Fin (m+1)) : MemLp (WeakSobolevJet.parameterTimeField w.q (ρ.multiplier w τ) Jt k) 2 g.timeMeasure := by
    simpa only [one_mul] using WeakSobolevJet.memLp_parameterTimeField g w ρ τ 1 hw.aestronglyMeasurable hJ k
  have hfS (k : Fin (m+1)) : MemLp (WeakSobolevJet.parameterTimeField w.q (ρ.multiplier w τ)
      (s.extension g Js) k) 2 g.timeMeasure := by
    simpa only [one_mul] using WeakSobolevJet.memLp_parameterTimeField g w ρ τ 1 hw.aestronglyMeasurable hJs k
  have hcellE : WeakSobolevJet.spacetimeWeightedNorm g w.q (ρ.multiplier w τ) (s.extension g Js) ≤
      3*energyNorm hS hν a.sobolev g ρ w τ es :=
    WeakSobolevJet.spacetimeWeightedNorm_extension_le g s w ρ hw hτStar hτ hmesh Js
  have hsEc := hcellE.trans (mul_le_mul_of_nonneg_left hsE (by norm_num))
  let esH : g.Sequence (Lp ℝ 2 ν) := fun i => (u i : Lp ℝ 2 ν)-r.RH (z i)
  have hcell0 : bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map (s.extension g esH t)) ≤
      3*g.l2Norm (ρ.nodeMap g w τ esH) := by
    rw [ρ.timeMap_extension_bochnerNorm g w τ hw.aestronglyMeasurable]
    have hh := (ρ.timeMap_extension_norm_comparison hw s τ (τStar+m) (by positivity)
      (hτ.trans (le_add_of_nonneg_right (Nat.cast_nonneg m))) hmesh esH).1
    rw [← ρ.nodeMap_l2Norm g w τ] at hh
    exact hh
  have hs0c := hcell0.trans (mul_le_mul_of_nonneg_left hs0 (by norm_num))
  have hl2eq : (fun t => (ρ.multiplier w τ t).map (p.toTrajectory.value t-r.RH (s.extension g z t))) =
      (fun t => (ρ.multiplier w τ t).map
        (p.toTrajectory.value t-s.extension g (fun i => (u i : Lp ℝ 2 ν)) t)+
        (ρ.multiplier w τ t).map (s.extension g esH t)) := by
    funext t
    rw [← BoundedMultiplier.map_add]
    congr 1
    cases s <;> dsimp only [Orientation.extension,TimeGrid.extensionPlus,TimeGrid.extensionMinus,esH] <;> abel
  have htLp := ρ.memLp_map w τ hw.aestronglyMeasurable
    (p.toTrajectory.value_L2.sub (s.memLp_extension g (fun i => (u i : Lp ℝ 2 ν))))
  have hsLp := ρ.memLp_map w τ hw.aestronglyMeasurable (s.memLp_extension g esH)
  refine ⟨?_,?_,?_⟩
  · rw [hl2eq]
    have hh := (bochnerL2Norm_add htLp hsLp).trans (add_le_add ht0 hs0c)
    have hr := combine_nonnegative_rates hKt (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hKs)
      g.dt_pos.le (show 0 ≤ a0+aE^2+ηA by positivity) (g.l2Norm_nonneg (ρ.nodeMap g w τ f))
    exact hh.trans (by convert hr using 1 <;> ring)
  · rw [heq]
    exact hJ.add hJs
  · rw [heq]
    have hh := (WeakSobolevJet.spacetimeWeightedNorm_add_le g w.q (ρ.multiplier w τ)
      Jt (s.extension g Js) hfT hfS).trans (add_le_add htE hsEc)
    have hr := combine_nonnegative_rates hKt (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hKs)
      (Real.sqrt_nonneg g.dt) (add_nonneg haE hη) (g.l2Norm_nonneg (ρ.nodeMap g w τ f))
    exact hh.trans (by convert hr using 1 <;> ring)

end Carleman.Section4
