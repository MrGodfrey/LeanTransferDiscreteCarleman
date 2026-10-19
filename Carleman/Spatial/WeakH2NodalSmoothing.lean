module

public import Carleman.Spatial.WeakH2ClosureContinuous

/-! One actual smooth sequence converges strongly in every original H²
component and pointwise to any genuine closed-domain continuous representative.
The representative is identified by uniqueness, not by an assumed smooth lift. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem WeakSobolevJet.exists_smooth_h2_pointwise_approximation
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    {a : SpatialCoordinates d} (ha : a ∈ S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {f : SpatialCoordinates d → ℝ} (hf : ContinuousOn f (closure S))
    (hfu : f =ᵐ[volume.restrict S] WeakSobolevJet.value u) :
    ∃ F : ℕ → SpatialCoordinates d → ℝ,
      (∀ n, ContDiff ℝ ∞ (F n)) ∧
      (∀ x ∈ closure S, Tendsto (fun n => F n x) atTop (𝓝 (f x))) ∧
      (Tendsto (fun n => bochnerL2Norm (volume.restrict (closure S))
        (fun x => F n x-zeroExtendLp hS.measurableSet (WeakSobolevJet.value u) x)) atTop (𝓝 0)) ∧
      (∀ v : Fin 1 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict (closure S))
        (fun x => coordinateDerivative v (F n) x-
          zeroExtendLp hS.measurableSet (derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u)) x)) atTop (𝓝 0)) ∧
      (∀ v : Fin 2 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict (closure S))
        (fun x => coordinateDerivative v (F n) x-
          zeroExtendLp hS.measurableSet (derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u)) x)) atTop (𝓝 0)) := by
  obtain ⟨φ,_,hs,ht₀,ht₁,ht₂⟩ := WeakSobolevJet.inward_mollification_strong_h2 hS hc hb ha u
  let w := zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)
  let F := inwardMollification a φ w
  let b := fun v : Fin 1 → Fin d => zeroExtendLp hS.measurableSet
    (derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u))
  let c := fun v : Fin 2 → Fin d => zeroExtendLp hS.measurableSet
    (derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u))
  have hK : IsCompact (closure S) := isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hvol : 0 < volume.real (closure S) := ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume
      ⟨a,interior_mono subset_closure (hS.interior_eq.symm ▸ ha)⟩).ne' hK.measure_ne_top
  obtain ⟨g,hg,hu⟩ := convex_smooth_h2_uniform_limit hK hc.closure hvol hd
    (fun n => (hs n).of_le (by simp)) ((Lp.memLp w).restrict (closure S))
    (fun v => (Lp.memLp (b v)).restrict (closure S))
    (fun v => (Lp.memLp (c v)).restrict (closure S)) ht₀ ht₁ ht₂
    diam_nonneg (fun _ hx _ hy => dist_le_diam_of_mem hb.closure hx hy)
  have hgw : g =ᵐ[volume.restrict (closure S)] w :=
    l2_limit_ae_eq_of_ae_tendsto ((Lp.memLp w).restrict (closure S))
      (continuousOn_memLp_compact hK hg)
      (fun n => continuous_memLp_compact hK (hs n).continuous) ht₀
      ((ae_restrict_mem hK.measurableSet).mono fun x hx => hu.tendsto_at hx)
  have hgu : g =ᵐ[volume.restrict S] WeakSobolevJet.value u :=
    (hgw.filter_mono (ae_mono (Measure.restrict_mono subset_closure le_rfl))).trans
      (zeroExtendLp_ae_restrict hS.measurableSet (WeakSobolevJet.value u))
  have he := WeakSobolevJet.closure_continuous_representative_unique hS u hg hf hgu hfu
  exact ⟨F,hs,fun x hx => he hx ▸ hu.tendsto_at hx,ht₀,ht₁,ht₂⟩

end Carleman
