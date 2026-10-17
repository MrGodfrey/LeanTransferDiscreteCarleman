module

public import Carleman.Continuous.TemporalEnergyError

/-! Function-level error for the original associated operator. The continuous
solution has only a.e. D(A) values, a true H weak derivative and periodic H traces.
The Bochner norm comparison includes an explicit finiteness conclusion. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
namespace TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
theorem error_bochner_eq (s : Orientation) (u : ℝ → H) (U : Lp H 2 g.timeMeasure)
    (hu : U =ᵐ[g.timeMeasure] u) (v : g.Sequence H) :
    MemLp (fun t => u t - s.extension g v t) 2 g.timeMeasure ∧
      bochnerL2Norm g.timeMeasure (fun t => u t - s.extension g v t) = ‖U - s.extensionLp g v‖ := by
  have hm := ((Lp.memLp U).ae_eq hu).sub (s.memLp_extension g v)
  change MemLp (fun t => u t - s.extension g v t) 2 g.timeMeasure at hm
  refine ⟨hm, ?_⟩
  rw [bochnerL2Norm_eq _ hm]
  congr 1
  apply Lp.ext
  filter_upwards [hm.coeFn_toLp,Lp.coeFn_sub U (s.extensionLp g v),hu,s.extensionLp_ae g v]
    with t ht hs hu hv
  simp only [Pi.sub_apply] at hs
  rw [ht,hs,hu,hv]
end TimeGrid

namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

/-- Transfer the proved error to the original A1 domain/operator, with real
Bochner norms and original weak regularity. No weighted conclusion is claimed. -/
theorem IsAssociated.temporal_weak_error_uniform {D : Submodule ℝ H} {A : D →ₗ[ℝ] H}
    (hA : b.IsAssociated A) (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ : 0 < β) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → ∀ f : g.Sequence H,
        let μ := fun i => (L*w.nodes g i)^(2*m)
        let hμ : ∀ i, 0 ≤ μ i := fun _ => (even_two_mul m).pow_nonneg _
        let u := fun i => (b.eulerSolution g s μ hμ f i : H)
        ∃ U : PeriodicWeakTrajectory g D A,
          (∀ᵐ t ∂g.timeMeasure, s.sign • U.derivative t + A (U.domainValue t) +
            s.extension g μ t • U.value t = s.extension g f t) ∧
          MemLp (fun t => U.value t - s.extension g u t) 2 g.timeMeasure ∧
          bochnerL2Norm g.timeMeasure (fun t => U.value t - s.extension g u t) ≤
            12*g.dt*g.l2Norm f := by
  have hd := hA.domain_eq b
  subst D
  have ha := hA.operator_eq b
  subst A
  obtain ⟨L₀,δ,hL₀,hδ,hsolve⟩ := b.temporal_l2_error_uniform m hm β hβ
  refine ⟨L₀,δ,hL₀,hδ,?_⟩
  intro g s w h L hL hmesh f μ hμ u
  obtain ⟨p,hp,_⟩ := hsolve g s w h L hL hmesh f
  have he := g.error_bochner_eq s p.toTrajectory.value (g.pathL2 p.val.1) (g.pathL2_ae p.val.1) u
  refine ⟨p.toTrajectory,?_,he.1,he.2.trans_le hp.2.2⟩
  have hp' := (b.evolution_eq_iff g s (s.frozenMultiplier g μ) p (s.extensionLp g f)).mp hp.1
  filter_upwards [hp',s.extensionLp_ae g f] with t ht hf
  exact ht.trans hf
end CoerciveForm
end Carleman
