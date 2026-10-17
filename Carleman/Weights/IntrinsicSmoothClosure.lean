module

public import Carleman.Weights.SmoothClosure
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Intrinsic smoothness up to the boundary. Actual derivatives are taken only
in the open domain. Their continuous extensions, not derivatives of arbitrary
off-domain values, are used on the closure. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff BigOperators
namespace Carleman

def tensorCoordinates {d k : ℕ} :
    (SpatialCoordinates d [×k]→L[ℝ] ℝ) →L[ℝ] ((Fin k → Fin d) → ℝ) :=
  ContinuousLinearMap.pi coordinateTensorEval

theorem tensorCoordinates_injective {d k : ℕ} :
    Function.Injective (tensorCoordinates (d := d) (k := k)) := by
  intro A B h
  have he : A.toMultilinearMap = B.toMultilinearMap :=
    Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      (fun v => congrFun h v)
  ext x
  exact congrArg (fun F : MultilinearMap ℝ (fun _ : Fin k => SpatialCoordinates d) ℝ => F x) he

/-- A continuous reconstruction from the finite array of all tensor entries.
No choice of a boundary extension operator is involved. -/
def tensorReconstruction {d k : ℕ} :
    ((Fin k → Fin d) → ℝ) →L[ℝ] (SpatialCoordinates d [×k]→L[ℝ] ℝ) :=
  (tensorCoordinates (d := d) (k := k)).toLinearMap.leftInverse.toContinuousLinearMap

theorem tensorReconstruction_coordinates {d k : ℕ} (A : SpatialCoordinates d [×k]→L[ℝ] ℝ) :
    tensorReconstruction (tensorCoordinates A) = A :=
  LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr tensorCoordinates_injective) A

/-- The profile itself is continuous on the closure, is smooth in the domain,
and every interior Fréchet derivative admits a continuous extension. -/
def SmoothOnClosure {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (S : Set (SpatialCoordinates d)) : Prop :=
  ContinuousOn f (closure S) ∧ ContDiffOn ℝ ∞ f S ∧
    ∀ k : ℕ, ∃ F : SpatialCoordinates d → (SpatialCoordinates d [×k]→L[ℝ] ℝ),
      ContinuousOn F (closure S) ∧ EqOn F (iteratedFDeriv ℝ k f) S

/-- The equivalent description by all actual iterated coordinate derivatives. -/
def CoordinateSmoothOnClosure {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (S : Set (SpatialCoordinates d)) : Prop :=
  ContinuousOn f (closure S) ∧ ContDiffOn ℝ ∞ f S ∧
    ∀ (k : ℕ) (v : Fin k → Fin d), ∃ F : SpatialCoordinates d → ℝ,
      ContinuousOn F (closure S) ∧ EqOn F (coordinateDerivative v f) S

theorem smoothOnClosure_iff_coordinate {d : ℕ} {f : SpatialCoordinates d → ℝ}
    {S : Set (SpatialCoordinates d)} : SmoothOnClosure f S ↔ CoordinateSmoothOnClosure f S := by
  constructor
  · rintro ⟨hc, hs, hd⟩
    refine ⟨hc, hs, fun k v => ?_⟩
    obtain ⟨F, hF, he⟩ := hd k
    exact ⟨fun x => coordinateTensorEval v (F x),
      (coordinateTensorEval v).continuous.comp_continuousOn hF,
      fun x hx => congrArg (coordinateTensorEval v) (he hx)⟩
  · rintro ⟨hc, hs, hd⟩
    refine ⟨hc, hs, fun k => ?_⟩
    choose F hF he using hd k
    refine ⟨fun x => tensorReconstruction (fun v => F v x),
      tensorReconstruction.continuous.comp_continuousOn (continuousOn_pi.mpr hF), ?_⟩
    intro x hx
    have hentries : (fun v => F v x) = tensorCoordinates (iteratedFDeriv ℝ k f x) := by
      funext v
      exact he v hx
    change tensorReconstruction (fun v => F v x) = _
    rw [hentries, tensorReconstruction_coordinates]

theorem SmoothOnClosure.of_neighborhood {d : ℕ} {f : SpatialCoordinates d → ℝ}
    {S U : Set (SpatialCoordinates d)} (hU : IsOpen U) (hSU : closure S ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) : SmoothOnClosure f S := by
  refine ⟨hf.continuousOn.mono hSU, hf.mono (subset_closure.trans hSU), fun k => ?_⟩
  refine ⟨iteratedFDeriv ℝ k f, ?_, fun _ _ => rfl⟩
  intro x hx
  exact ((hf.contDiffAt (hU.mem_nhds (hSU hx))).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt

theorem SmoothOnClosure.neg {d : ℕ} {f : SpatialCoordinates d → ℝ}
    {S : Set (SpatialCoordinates d)} (hf : SmoothOnClosure f S) : SmoothOnClosure (-f) S := by
  refine ⟨hf.1.neg, hf.2.1.neg, fun k => ?_⟩
  obtain ⟨F, hF, he⟩ := hf.2.2 k
  refine ⟨-F, hF.neg, ?_⟩
  intro x hx
  simpa only [Pi.neg_apply, iteratedFDeriv_neg_apply] using congrArg Neg.neg (he hx)

/-- The intrinsic condition is independent of all off-domain values. -/
theorem SmoothOnClosure.congr {d : ℕ} {f g : SpatialCoordinates d → ℝ}
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hf : SmoothOnClosure f S)
    (hfg : EqOn g f (closure S)) : SmoothOnClosure g S := by
  refine ⟨hf.1.congr hfg, hf.2.1.congr (fun x hx => hfg (subset_closure hx)), fun k => ?_⟩
  obtain ⟨F, hF, he⟩ := hf.2.2 k
  refine ⟨F, hF, ?_⟩
  intro x hx
  have heq : g =ᶠ[nhds x] f :=
    Filter.eventuallyEq_of_mem (hS.mem_nhds hx) (fun y hy => hfg (subset_closure hy))
  exact (he hx).trans (heq.iteratedFDeriv ℝ k).eq_of_nhds.symm

/-- Bounded derivatives are only asserted at interior points. This avoids
silently differentiating a discontinuous off-domain representative at a boundary. -/
def BoundedSmoothOn {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (S : Set (SpatialCoordinates d)) : Prop :=
  ContDiffOn ℝ ∞ f S ∧ ∀ n : ℕ, ∃ M : ℝ, 1 ≤ M ∧
    ∀ j, j ≤ n → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ M

theorem SmoothOnClosure.boundedSmoothOn {d : ℕ} {f : SpatialCoordinates d → ℝ}
    {S : Set (SpatialCoordinates d)} (hf : SmoothOnClosure f S)
    (hS : Bornology.IsBounded S) : BoundedSmoothOn f S := by
  refine ⟨hf.2.1, fun n => ?_⟩
  choose F hF he using hf.2.2
  choose C hC using fun j : Fin (n+1) =>
    hS.isCompact_closure.exists_bound_of_continuousOn (hF j.val)
  refine ⟨1 + ∑ j, max 0 (C j), ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => le_max_left _ _)
  · intro j hj x hx
    have hb := Finset.single_le_sum (s := Finset.univ) (f := fun k => max 0 (C k))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ (⟨j, by omega⟩ : Fin (n+1)))
    rw [← he j hx]
    exact (hC ⟨j, by omega⟩ x (subset_closure hx)).trans
      ((le_max_right _ _).trans (hb.trans (by linarith)))

end Carleman
