module

public import Carleman.Spatial.WeakH2ClosureSmoothing
public import Carleman.Spatial.L2LimitRepresentative
public import Carleman.Spatial.WeakH2Continuous

/-! In dimensions at most three, every original weak H² state on a bounded
open convex domain has a unique continuous representative on its closure.
It is obtained from the same actual smooth inward mollifications. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem WeakSobolevJet.inward_mollification_uniform_limit
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    {a : SpatialCoordinates d} (ha : a ∈ S)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ ∃ f : SpatialCoordinates d → ℝ,
      ContinuousOn f (closure S) ∧ f =ᵐ[volume.restrict S] WeakSobolevJet.value u ∧
      TendstoUniformlyOn
        (inwardMollification a φ (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)))
        f atTop (closure S) := by
  obtain ⟨φ,hφ,hs,ht₀,ht₁,ht₂⟩ := WeakSobolevJet.inward_mollification_strong_h2 hS hc hb ha u
  let w := zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)
  let U := inwardMollification a φ w
  let b := fun v : Fin 1 → Fin d => zeroExtendLp hS.measurableSet
    (derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u))
  let c := fun v : Fin 2 → Fin d => zeroExtendLp hS.measurableSet
    (derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u))
  have hK : IsCompact (closure S) := isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hvol : 0 < volume.real (closure S) := ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume
      ⟨a,interior_mono subset_closure (hS.interior_eq.symm ▸ ha)⟩).ne' hK.measure_ne_top
  obtain ⟨f,hf,hu⟩ := convex_smooth_h2_uniform_limit hK hc.closure hvol hd
    (fun n => (hs n).of_le (by simp)) ((Lp.memLp w).restrict (closure S))
    (fun v => (Lp.memLp (b v)).restrict (closure S))
    (fun v => (Lp.memLp (c v)).restrict (closure S)) ht₀ ht₁ ht₂
    diam_nonneg (fun _ hx _ hy => dist_le_diam_of_mem hb.closure hx hy)
  have hae : f =ᵐ[volume.restrict (closure S)] w :=
    l2_limit_ae_eq_of_ae_tendsto ((Lp.memLp w).restrict (closure S))
      (continuousOn_memLp_compact hK hf)
      (fun n => continuous_memLp_compact hK (hs n).continuous) ht₀
      ((ae_restrict_mem hK.measurableSet).mono fun x hx => hu.tendsto_at hx)
  refine ⟨φ,hφ,f,hf,?_,hu⟩
  exact (hae.filter_mono (ae_mono (Measure.restrict_mono subset_closure le_rfl))).trans
    (zeroExtendLp_ae_restrict hS.measurableSet (WeakSobolevJet.value u))

theorem WeakSobolevJet.exists_closure_continuous_representative
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    ∃ f : SpatialCoordinates d → ℝ, ContinuousOn f (closure S) ∧
      f =ᵐ[volume.restrict S] WeakSobolevJet.value u := by
  by_cases hn : S.Nonempty
  · obtain ⟨a,ha⟩ := hn
    obtain ⟨_,_,f,hf,hu,_⟩ := WeakSobolevJet.inward_mollification_uniform_limit hS hc hb hd ha u
    exact ⟨f,hf,hu⟩
  · have he : S=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    refine ⟨fun _ => 0,continuous_const.continuousOn,?_⟩
    simp only [he,Measure.restrict_empty,ae_zero,Filter.EventuallyEq,Filter.eventually_bot]

theorem WeakSobolevJet.closure_continuous_representative_unique
    (hS : IsOpen S) (u : WeakSobolevJet d 2 (volume.restrict S) S)
    {f g : SpatialCoordinates d → ℝ} (hf : ContinuousOn f (closure S)) (hg : ContinuousOn g (closure S))
    (hfu : f =ᵐ[volume.restrict S] WeakSobolevJet.value u)
    (hgu : g =ᵐ[volume.restrict S] WeakSobolevJet.value u) : EqOn f g (closure S) :=
  (WeakSobolevJet.continuous_representative_unique hS u (hf.mono subset_closure)
    (hg.mono subset_closure) hfu hgu).of_subset_closure hf hg subset_closure Subset.rfl

end Carleman
