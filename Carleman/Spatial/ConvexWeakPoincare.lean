module

public import Carleman.Spatial.InteriorWeakPoincare
public import Carleman.Geometry.ConvexCompactExhaustion
public import Carleman.Spatial.ComponentNorms

/-! Mean Poincaré for the original weak derivative states on bounded open
convex domains. Compact interior estimates pass to the whole domain by a
proved exhaustion and Fatou, without imposing a boundary trace. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem convex_weak_pairwise_bound (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S)
    (u : Lp ℝ 2 (volume.restrict S)) (v : Fin d → Lp ℝ 2 (volume.restrict S))
    (hv : ∀ i, IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    (∫ x in S, ∫ y in S, (u x-u y)^2) ≤
      (2:ℝ)^d*volume.real S*D^2*(∑ i : Fin d, ‖v i‖^2) := by
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top (μ := volume)⟩
  rcases eq_empty_or_nonempty S with hE | ⟨a,ha⟩
  · subst S
    simp
  let K := convexInnerCompact S a
  have hK (n : ℕ) : IsCompact (K n) := convexInnerCompact_compact hb a n
  have hsub (n : ℕ) : K n ⊆ S := convexInnerCompact_subset hS hc ha n
  have hm := pairwise_memLp (Lp.memLp u)
  rw [← integral_prod _ hm.integrable_sq]
  apply l2_square_bound_on_exhaustion hm (fun n => K n ×ˢ K n)
    (fun n => (hK n).measurableSet.prod (hK n).measurableSet) ?_ (by positivity)
  · intro n
    rw [← Measure.prod_restrict,Measure.restrict_restrict_of_subset (hsub n)]
    have huK : MemLp u 2 (volume.restrict (K n)) := by
      have hh := (Lp.memLp u).restrict (K n)
      rwa [Measure.restrict_restrict_of_subset (hsub n)] at hh
    let : IsFiniteMeasure (volume.restrict (K n)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using (hK n).measure_lt_top⟩
    rw [integral_prod _ (pairwise_memLp huK).integrable_sq]
    have he := interior_weak_pairwise hS (hK n) (convexInnerCompact_convex hc a n) (hsub n)
      u v hv hD (fun x hx y hy => hdiam x (hsub n hx) y (hsub n hy))
    have hvol : volume.real (K n) ≤ volume.real S := measureReal_mono (hsub n)
      (hb.measure_lt_top (μ := volume)).ne
    have hp : 0 ≤ (2:ℝ)^d*D^2*(∑ i : Fin d, ‖v i‖^2) := by positivity
    exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hvol hp])
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hS.measurableSet),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hS.measurableSet)] with p hp hq
    exact (convexInnerCompact_eventually_mem hS a hp).and (convexInnerCompact_eventually_mem hS a hq)

theorem convex_weak_mean_poincare (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S)
    (hvol : 0 < volume.real S)
    (u : Lp ℝ 2 (volume.restrict S)) (v : Fin d → Lp ℝ 2 (volume.restrict S))
    (hv : ∀ i, IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    (∫ x in S, (u x-(∫ y in S, u y)/volume.real S)^2) ≤
      (2:ℝ)^d/2*D^2*(∑ i : Fin d, ‖v i‖^2) := by
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top (μ := volume)⟩
  have he := mean_square_pairwise_identity (Lp.memLp u) (by simpa using hvol)
  simp only [measureReal_restrict_apply_univ] at he
  apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0:ℝ) < 2) hvol)).mp
  rw [he]
  exact (convex_weak_pairwise_bound hS hc hb u v hv hD hdiam).trans_eq (by ring)

theorem convex_weakJet_mean_poincare (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S)
    (hvol : 0 < volume.real S) (u : WeakSobolevJet d 1 (volume.restrict S) S)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    (∫ x in S, (WeakSobolevJet.value u x-(∫ y in S, WeakSobolevJet.value u y)/volume.real S)^2) ≤
      (2:ℝ)^d/2*D^2*‖WeakSobolevJet.field 1 u‖^2 := by
  have he := convex_weak_mean_poincare hS hc hb hvol (WeakSobolevJet.value u)
    (fun i => derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
    (fun i => WeakSobolevJet.field_weak_derivative u (0 : Fin 1) Sym.nil i) hD hdiam
  have hs : (∑ i : Fin d, ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)‖^2)=
      ‖WeakSobolevJet.field 1 u‖^2 := by
    rw [derivativeField_norm_sq]
    exact Equiv.sum_comp Sym.oneEquiv (fun α => ‖derivativeComponent α (WeakSobolevJet.field 1 u)‖^2)
  rwa [hs] at he

end Carleman
