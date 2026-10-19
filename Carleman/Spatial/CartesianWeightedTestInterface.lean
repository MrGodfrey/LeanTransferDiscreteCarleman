module

public import Carleman.Spatial.CartesianPhysicalTest
public import Carleman.Spatial.AllowedCartesianTestSuperapproximation
public import Carleman.Control.FullP1Superapproximation
public import Carleman.Section4.TestData

/-! The same original Cartesian diagonal test supplies the full WeightedTest
interface, with constants fixed before every grid, period and allowed weight. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem cartesian_weightedTest_interface
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 2 ρ.value (closure S))
    (κ β τStar : ℝ) (hκ : 0 < κ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ ε > (0:ℝ), ε ≤ 1 ∧ ∃ Ctime > (0:ℝ), ∃ Csuper > (0:ℝ),
    ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hdom : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=S) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
    ∀ (w : TimeWeight) (g : TimeGrid) (H : TimeWeightRegularity w g β)
      (τ η : ℝ), |τ| ≤ τStar → |η|=1 → h*w.max ≤ ε →
    ∃ T : Section4.WeightedTest hS
      (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S)
      (hdom ▸ cartesianReconstruction o δ hδ N) g (ρ.scaled η) w τ Ctime Csuper h,
      T.op=(fun t => (cartesianPhysicalTest o δ hδ N ρ.value w τ η t).toLinearMap) ∧
      T.derivative=(fun t => (cartesianPhysicalTestDerivative o δ hδ N ρ.value H τ η t).toLinearMap) := by
  obtain ⟨ε,hε,Csuper,hCs,hsuper⟩ :=
    allowed_weight_cartesian_test_superapproximation hS hc hcompact ρ hρ κ hκ
  obtain ⟨Ctime,hCt,htime⟩ := allowed_weight_cartesian_test_time hS hc hcompact ρ
    (hρ.of_le (by norm_num)) β τStar hβ hτStar
  refine ⟨min 1 ε,lt_min zero_lt_one hε,min_le_left _ _,Ctime,hCt,Csuper,hCs,?_⟩
  intro o δ hδ N hdom h hh hlower hupper w g H τ η hτ hη hsmall
  subst S
  let hν := ae_restrict_mem (μ := volume) hS.measurableSet
  let hV := dirichletSubspace_sobolev (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
  let r := cartesianReconstruction o δ hδ N
  have hqt (t : ℝ) : h*w.q t ≤ min 1 ε :=
    (mul_le_mul_of_nonneg_left (w.upper t) hh.le).trans hsmall
  let T : Section4.WeightedTest hS hν hV r g (ρ.scaled η) w τ Ctime Csuper h := {
    op := fun t => (cartesianPhysicalTest o δ hδ N ρ.value w τ η t).toLinearMap
    derivative := fun t => (cartesianPhysicalTestDerivative o δ hδ N ρ.value H τ η t).toLinearMap
    endpoint := congrArg ContinuousLinearMap.toLinearMap (cartesianPhysicalTest_endpoint o δ hδ N ρ.value H τ η)
    hasDeriv := fun z _ ht => cartesianPhysicalTest_pairing_hasDerivWithinAt o δ hδ N ρ.value H τ η ht z
    symmetric := fun t _ v z => cartesianPhysicalTest_symmetric o δ hδ N ρ.value w τ η t v z
    nonneg := fun t _ z => cartesianPhysicalTest_nonneg o δ hδ N ρ.value w τ η t z
    time_bound := by
      intro z t ht
      have hb := htime o δ hδ N (Subset.refl _) h hh hupper w g H τ η t hτ hη ht
        ((hqt t).trans (min_le_left _ _)) (fun a => z a)
      change |inner ℝ z (cartesianPhysicalTestDerivative o δ hδ N ρ.value H τ η t z)| ≤ _
      rw [cartesianPhysicalState_inner]
      change |cartesianPhysicalInner δ N (fun a => z a)
        (cartesianAllowedTestDerivative o δ N ρ.value H τ η t (fun a => z a))| ≤ _
      calc
        _ ≤ Ctime*(w.q t)^2*
            (((ρ.scaled η).multiplier w τ t).seminorm (r.RH z))^2 := hb
        _ = _ := by ring
    superapprox := by
      intro t _ hw z
      let σ := (ρ.scaled η).multiplier w τ t
      let v := r.R (cartesianPhysicalTest o δ hδ N ρ.value w τ η t z)-
        conformingWeight σ hw (conformingWeight σ hw (r.R z))
      obtain ⟨e,he,hn⟩ := hsuper o δ hδ N rfl h hh hlower hupper w τ t η hη
        ((hqt t).trans (min_le_right _ _)) (fun a => z a)
      have hid : e=domainSobolevJet hS hν hV v := by
        apply WeakSobolevJet.value_injective hS hν
        rw [he,domainSobolevJet_value]
        change cartesianKuhnReconstructionLp o δ hδ N
          (cartesianSquaredWeightTest o δ N σ.value (fun a => z a))-
          (σ.mul σ).map (r.RH z)=
          r.RH (cartesianPhysicalTest o δ hδ N ρ.value w τ η t z)-σ.map (σ.map (r.RH z))
        rw [BoundedMultiplier.mul_map]
        rfl
      have hu : cartesianKuhnReconstructionJet o δ hδ N (fun a => z a)=
          domainSobolevJet hS hν hV (r.R z) := by
        apply WeakSobolevJet.value_injective hS hν
        rw [cartesianKuhnReconstructionJet_value,domainSobolevJet_value]
        rfl
      rw [hid,hu,SpatialProfile.scaled_neg] at hn
      exact hn }
  exact ⟨T,rfl,rfl⟩

end Carleman
