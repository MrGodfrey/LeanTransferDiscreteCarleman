module

public import Carleman.Transfer.Load
public import Carleman.Periodic.CellExtension

/-!
# Cancellation of the auxiliary load in the continuous residual

This is the algebra of `eq:transfer-residual` in Section 5, Step 1. The spatial
operator acts on its domain `D ⊆ H`, not on all of `H`; the reconstruction
only has to lie in `V ⊆ H`. `dU` denotes the supplied time derivative in `H`
(e.g. the weak derivative of the future frozen solution). No claim of
existence, differentiability, or a graph estimate is made by this interface.

The exact frozen equation is a premise of the cancellation identity. A filter
version preserves its almost-everywhere interpretation: the future Sobolev
interface can instantiate the filter by volume restricted to `(0,T)` without
strengthening the PDE to an everywhere equation. The type `U : ℝ → D` here
is a chosen domain-valued representative for this algebra. The future B1
interface must construct or transfer an almost-everywhere `D(A)`-valued
representative of the actual Sobolev solution, preserving its `H`-valued weak
derivative and endpoint traces; this interface does not show that its original
representative belongs to `D(A)` at every time. Both half-open cell choices
are concrete and share the extensions of the shift, load, and state.
-/

@[expose] public section

namespace Carleman.LoadInterface

variable {H X : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {V : Submodule ℝ H} {r : Reconstruction V X}
variable {F : Type*}
variable (l : LoadInterface r F) (g : TimeGrid)

/-- Extend the transfer load on the positive-orientation cells. -/
theorem extensionPlus_transferLoad (μ : g.Sequence ℝ) (f : g.Sequence F)
    (z : g.Sequence X) (t : ℝ) :
    g.extensionPlus (l.transferLoad g μ f z) t =
      g.extensionPlus (fun i => l.lift (f i)) t +
        g.extensionPlus μ t • r.RH (g.extensionPlus z t) := rfl

theorem extensionMinus_transferLoad (μ : g.Sequence ℝ) (f : g.Sequence F)
    (z : g.Sequence X) (t : ℝ) :
    g.extensionMinus (l.transferLoad g μ f z) t =
      g.extensionMinus (fun i => l.lift (f i)) t +
        g.extensionMinus μ t • r.RH (g.extensionMinus z t) := rfl

private theorem cancel_shift (p u b v : H) (μ : ℝ)
    (h : p + μ • u = b + μ • v) : p = b - μ • (u - v) := by
  rw [smul_sub]
  have hp : p = b + μ • v - μ • u := eq_sub_of_add_eq h
  rw [hp]
  abel

/-- The residual identity at any time where the frozen equation holds.
`ε = 1` and `ε = -1` give the paper's two orientations. -/
theorem residualPlus_eq {D : Submodule ℝ H} (A : D →ₗ[ℝ] H)
    (ε : ℝ) (U : ℝ → D) (dU : ℝ → H)
    (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X) (t : ℝ)
    (hFrozen : ε • dU t + A (U t) + g.extensionPlus μ t • (U t : H) =
      g.extensionPlus (l.transferLoad g μ f z) t) :
    ε • dU t + A (U t) = g.extensionPlus (fun i => l.lift (f i)) t -
      g.extensionPlus μ t • ((U t : H) - r.RH (g.extensionPlus z t)) := by
  rw [l.extensionPlus_transferLoad] at hFrozen
  exact cancel_shift _ _ _ _ _ hFrozen

theorem residualMinus_eq {D : Submodule ℝ H} (A : D →ₗ[ℝ] H)
    (ε : ℝ) (U : ℝ → D) (dU : ℝ → H)
    (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X) (t : ℝ)
    (hFrozen : ε • dU t + A (U t) + g.extensionMinus μ t • (U t : H) =
      g.extensionMinus (l.transferLoad g μ f z) t) :
    ε • dU t + A (U t) = g.extensionMinus (fun i => l.lift (f i)) t -
      g.extensionMinus μ t • ((U t : H) - r.RH (g.extensionMinus z t)) := by
  rw [l.extensionMinus_transferLoad] at hFrozen
  exact cancel_shift _ _ _ _ _ hFrozen

/-- In particular this applies almost everywhere, without an everywhere PDE premise. -/
theorem residualPlus_eventuallyEq (φ : Filter ℝ) {D : Submodule ℝ H}
    (A : D →ₗ[ℝ] H) (ε : ℝ) (U : ℝ → D) (dU : ℝ → H)
    (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X)
    (hFrozen : ∀ᶠ t in φ, ε • dU t + A (U t) + g.extensionPlus μ t • (U t : H) =
      g.extensionPlus (l.transferLoad g μ f z) t) :
    ∀ᶠ t in φ, ε • dU t + A (U t) = g.extensionPlus (fun i => l.lift (f i)) t -
      g.extensionPlus μ t • ((U t : H) - r.RH (g.extensionPlus z t)) :=
  hFrozen.mono fun t ht => l.residualPlus_eq g A ε U dU μ f z t ht

theorem residualMinus_eventuallyEq (φ : Filter ℝ) {D : Submodule ℝ H}
    (A : D →ₗ[ℝ] H) (ε : ℝ) (U : ℝ → D) (dU : ℝ → H)
    (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X)
    (hFrozen : ∀ᶠ t in φ, ε • dU t + A (U t) + g.extensionMinus μ t • (U t : H) =
      g.extensionMinus (l.transferLoad g μ f z) t) :
    ∀ᶠ t in φ, ε • dU t + A (U t) = g.extensionMinus (fun i => l.lift (f i)) t -
      g.extensionMinus μ t • ((U t : H) - r.RH (g.extensionMinus z t)) :=
  hFrozen.mono fun t ht => l.residualMinus_eq g A ε U dU μ f z t ht

end Carleman.LoadInterface
