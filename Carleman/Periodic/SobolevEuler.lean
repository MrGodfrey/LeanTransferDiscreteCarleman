module

public import Carleman.Spatial.ConformingHilbert
public import Carleman.Continuous.FormAssociated
public import Carleman.Continuous.SobolevGraph

/-! Instantiate cyclic well-posedness on the original conforming Sobolev
space and bound the genuine weak derivative fields from original A1.
The scaled intermediate derivative interpolation is not assumed or claimed. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  (V : Submodule ℝ (Lp ℝ 2 ν)) (hV : V ≤ sobolevSubspace d m ν S)
  (hd : Dense (V : Set (Lp ℝ 2 ν)))
  (a : conformingHilbert (m := m) (S := S) V →L[ℝ]
    conformingHilbert (m := m) (S := S) V →L[ℝ] ℝ)
  (hsym : ∀ u v, a u v = a v u)
  (hcoer : ∃ c > (0 : ℝ), ∀ u, c*‖u‖*‖u‖ ≤ a u u)

/-- Existence and uniqueness for the original spatial operator A, from
closed dense conforming V and its original associated-form definition. -/
theorem conformingEuler_existsUnique
    (hc : IsClosed {u : WeakSobolevJet d m ν S | WeakSobolevJet.value u ∈ V})
    {D : Submodule ℝ (Lp ℝ 2 ν)} (A : D →ₗ[ℝ] Lp ℝ 2 ν)
    (hA : (conformingCoerciveForm V hS hν hV hd a hsym hcoer).IsAssociated A)
    (g : TimeGrid) (s : Orientation) (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (f : g.Sequence (Lp ℝ 2 ν)) :
    ∃! u : g.Sequence D, ∀ i,
      s.difference g (fun k => (u k : Lp ℝ 2 ν)) i + A (u i) +
        μ i • (u i : Lp ℝ 2 ν) = f i := by
  let := conformingHilbert_completeSpace V hc
  exact hA.existsUnique_periodicEuler _ g s μ hμ f

omit V hV hd a hsym hcoer in
/-- A1 elliptic regularity controls each actual L² weak derivative sequence.
This is unscaled; no parameter interpolation is hidden in its hypotheses. -/
theorem euler_sobolev_fields_bound {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (b : CoerciveForm (Lp ℝ 2 ν) W) {D : Submodule ℝ (Lp ℝ 2 ν)}
    (A : D →ₗ[ℝ] Lp ℝ 2 ν) (hA : b.IsAssociated A)
    (hD : D ≤ sobolevSubspace d (2*m) ν S) (C : ℝ) (hC : 0 ≤ C)
    (hell : ∀ u : D, ‖domainSobolevJet hS hν hD u‖ ≤ C*‖A u‖)
    (hm : 0 < m) {β L : ℝ} (hL : eulerShiftThreshold m β ≤ L)
    (g : TimeGrid) (w : TimeWeight) (hw : TimeWeightRegularity w g β)
    (hmesh : g.dt*w.max^2 ≤ cellThreshold β 0 0) (s : Orientation) (u : g.Sequence D) :
    (∑ k : Fin (2*m+1), g.l2Norm (fun i => WeakSobolevJet.field k
      (domainSobolevJet hS hν hD (u i)))) ≤
      (2*m+1 : ℝ)*C*3*g.l2Norm (fun i => s.difference g (fun k => (u k : Lp ℝ 2 ν)) i +
        A (u i) + (L*w.nodes g i)^(2*m) • (u i : Lp ℝ 2 ν)) := by
  have hgraph := hA.euler_unweighted_graph b hm hL g w hw hmesh s u
  have hfield (k : Fin (2*m+1)) : g.l2Norm (fun i => WeakSobolevJet.field k
      (domainSobolevJet hS hν hD (u i))) ≤ C*g.l2Norm (fun i => A (u i)) :=
    g.l2Norm_le_of_bound _ _ hC fun i => (WeakSobolevJet.norm_field_le k _).trans (hell (u i))
  have hs := Finset.sum_le_sum (s := Finset.univ) fun k _ => hfield k
  have hA0 : g.l2Norm (fun i => A (u i)) ≤ 3*g.l2Norm (fun i =>
      s.difference g (fun k => (u k : Lp ℝ 2 ν)) i + A (u i) +
        (L*w.nodes g i)^(2*m) • (u i : Lp ℝ 2 ν)) := by
    linarith [g.l2Norm_nonneg (s.difference g (fun k => (u k : Lp ℝ 2 ν))),
      g.l2Norm_nonneg (fun i => (L*w.nodes g i)^(2*m) • (u i : Lp ℝ 2 ν))]
  calc
    _ ≤ (2*m+1 : ℝ)*C*g.l2Norm (fun i => A (u i)) := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_assoc] using hs
    _ ≤ (2*m+1 : ℝ)*C*(3*g.l2Norm _) :=
      mul_le_mul_of_nonneg_left hA0 (by positivity)
    _ = _ := by ring

end Carleman
