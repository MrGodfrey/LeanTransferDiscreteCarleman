module

public import Carleman.Weights.WeightedGraphConstruction

/-! The graph remainder is precisely the manuscript's conjugated spatial
commutator, on the canonical a.e. domain representatives. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.CoerciveForm
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm (Lp ℝ 2 ν) V) (ρ : SpatialProfile ν)
  (g : TimeGrid) (w : TimeWeight) (τ : ℝ)
  (hq : AEStronglyMeasurable w.q g.timeMeasure)
  (hw : ∀ t (u : b.domain), (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ b.domain)
  (hξ : ∀ t (u : b.domain), (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ b.domain)

/-- Only equality of the weighted L² class is required. -/
theorem weighted_graph_domain_ae (p q : b.PeriodicGraph g)
    (hv : g.pathL2 q.val.1 = ρ.timeMap g w τ hq (g.pathL2 p.val.1)) :
    q.toTrajectory.domainValue =ᵐ[g.timeMeasure]
      (fun t => conformingWeight (ρ.multiplier w τ t) (hw t) (p.toTrajectory.domainValue t)) := by
  filter_upwards [q.toTrajectory.domainValue_ae,p.toTrajectory.domainValue_ae,
    g.pathL2_ae q.val.1,g.pathL2_ae p.val.1,
    ρ.timeMap_ae g w τ hq (g.pathL2 p.val.1)] with t h1 h2 h3 h4 h5
  change g.pathL2 q.val.1 t = q.toTrajectory.value t at h3
  change g.pathL2 p.val.1 t = p.toTrajectory.value t at h4
  apply Subtype.ext
  change (q.toTrajectory.domainValue t : Lp ℝ 2 ν) =
    (ρ.multiplier w τ t).map (p.toTrajectory.domainValue t : Lp ℝ 2 ν)
  rw [h1,h2,← h3,hv,h5,h4]

theorem weighted_graph_commutator_ae (p q : b.PeriodicGraph g)
    (hv : g.pathL2 q.val.1 = ρ.timeMap g w τ hq (g.pathL2 p.val.1)) :
    (q.val.2.2 - ρ.timeMap g w τ hq p.val.2.2) =ᵐ[g.timeMeasure]
      allowedCommutatorPath b.operator ρ w τ hw hξ q.toTrajectory.domainValue := by
  filter_upwards [b.weighted_graph_domain_ae ρ g w τ hq hw p q hv,
    Lp.coeFn_sub q.val.2.2 (ρ.timeMap g w τ hq p.val.2.2),
    q.toTrajectory_operator_ae, p.toTrajectory_operator_ae,
    ρ.timeMap_ae g w τ hq p.val.2.2] with t hd hs hqA hpA hM
  simp only [Pi.sub_apply] at hs
  rw [hs,hM,← hqA,← hpA,allowedCommutatorPath_eq]
  have hi : conformingWeight (ρ.neg.multiplier w (-τ) t) (hξ t) (q.toTrajectory.domainValue t) =
      p.toTrajectory.domainValue t := by
    rw [hd]
    apply Subtype.ext
    exact BoundedMultiplier.map_inverse _ _
      (Filter.Eventually.of_forall fun x => by rw [mul_comm]; exact ρ.multiplier_inverse w τ t x) _
  rw [hi]

end Carleman.CoerciveForm
