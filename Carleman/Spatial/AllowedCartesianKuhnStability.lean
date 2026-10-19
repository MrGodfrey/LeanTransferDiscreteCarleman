module

public import Carleman.Spatial.CartesianKuhnWeightedNorm
public import Carleman.Geometry.KuhnAllowedWeightComparison
public import Carleman.Spatial.LocalWeightedNorm

/-! For a fixed original smooth profile, one constant controls the actual
Cartesian reconstruction and load for the complete allowed weight family.
It precedes every grid, time period, time weight, power, sign and state. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem allowed_weight_cartesianKuhn_stability
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S)) :
    ∃ C > 0, ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hTS : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ S)
      (h : ℝ), 0 < h → (∀ j, δ j ≤ h) →
      ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → h*w.q t ≤ 1 →
      ∀ f : CartesianInteriorIndex N → ℝ,
      let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
      let E := (∏ j, δ j)*(∑ a, (σ.value (cartesianInteriorPoint o δ N a)*f a)^2)
      E ≤ C*(σ.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2 ∧
      (σ.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2 ≤ C*E ∧
      (σ.seminorm (cartesianKuhnLoadLiftLp o δ hδ N f))^2 ≤ C*E := by
  obtain ⟨L,hL,hLip⟩ := smooth_profile_lipschitz hS hc hcompact hρ
  let W := Real.exp (L*(d:ℝ))
  have hW : 0 < W := Real.exp_pos _
  refine ⟨W^4*(d+2:ℝ),by positivity,?_⟩
  intro o δ hδ N hTS h hh hstep w τ t η hη hm f
  dsimp only
  let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
  let s : CartesianCellIndex N → ℝ := fun i => σ.value ((cartesianFiniteSimplex o δ hδ N i).points 0)
  have hpos (x : SpatialCoordinates d) : 0 < σ.value x := ρ.scaled_multiplier_pos η w τ t x
  have hs (i : CartesianCellIndex N) : 0 < s i := hpos _
  have hcomp (i : CartesianCellIndex N) {x : SpatialCoordinates d}
      (hx : x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) :
      |σ.value x| ≤ W*s i ∧ s i ≤ W*|σ.value x| :=
    cartesianKuhn_allowedWeight_comparison o δ hδ N hTS ρ L (by linarith) hLip h hh hstep
      w τ t η hη hm i hx (subset_convexHull ℝ _ (Set.mem_range_self 0))
  have hb (i : CartesianCellIndex N) (k : Fin (d+1)) :
      σ.value ((cartesianFiniteSimplex o δ hδ N i).points k) ≤ W*s i ∧
      s i ≤ W*σ.value ((cartesianFiniteSimplex o δ hδ N i).points k) := by
    simpa only [abs_of_pos (hpos _)] using
      hcomp i (subset_convexHull ℝ _ (Set.mem_range_self k))
  have hw (i : CartesianCellIndex N) :
      ∀ᵐ x ∂volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points),
      |σ.value x| ≤ W*s i ∧ s i ≤ W*|σ.value x| := by
    filter_upwards [ae_restrict_mem (simplicialCell_measurable (cartesianFiniteSimplex o δ hδ N i).points)] with x hx
    exact hcomp i hx
  have hbound := cartesianKuhn_weighted_norm_bounds o δ hδ N σ W hW s hs
    (fun _ _ => (hpos _).le) hb hw f
  refine ⟨hbound.1,?_,hbound.2.2⟩
  apply hbound.2.1.trans
  apply mul_le_mul_of_nonneg_right
  · have hd : (1:ℝ) ≤ d+2 := by exact_mod_cast Nat.le_add_left 1 (d+1)
    nlinarith [pow_nonneg hW.le 4]
  · exact mul_nonneg (Finset.prod_nonneg (fun j _ => (hδ j).le))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end Carleman
