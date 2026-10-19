module

public import Carleman.Spatial.CartesianWeightedTestInterface
public import Carleman.Spatial.CartesianPhysicalStability
public import Carleman.Spatial.CartesianHilbertObservation

/-! The full original weighted norm, load, positive test and observation
statements, including the properties not stored in the transfer interface. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2400000
open MeasureTheory Set
namespace Carleman
attribute [local instance] Classical.propDecidable

theorem cartesian_full_weight_interface {d : ℕ} {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 2 ρ.value (closure S))
    (κ β τStar : ℝ) (hκ : 0 < κ) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (ω₀ ω : Set (SpatialCoordinates d)) (hω₀ : MeasurableSet ω₀)
    (hcompact₀ : IsCompact (closure ω₀)) (hω : IsOpen ω) (hinc : closure ω₀ ⊆ ω) :
    ∃ ε > (0:ℝ), ε ≤ 1 ∧ ∃ Ctime > (0:ℝ), ∃ Csuper > (0:ℝ),
      ∃ Cmass > (0:ℝ), ∃ Cobs > (0:ℝ),
    ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hdom : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=S) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
    ∀ (w : TimeWeight) (g : TimeGrid) (H : TimeWeightRegularity w g β), h*w.max ≤ ε →
    ∀ (τ η : ℝ), |τ| ≤ τStar → |η|=1 →
    ∃ T : Section4.WeightedTest hS
      (ae_restrict_mem hS.measurableSet) (dirichletSubspace_sobolev S)
      (hdom ▸ cartesianReconstruction o δ hδ N) g (ρ.scaled η) w τ Ctime Csuper h,
      T.op=(fun t => (cartesianPhysicalTest o δ hδ N ρ.value w τ η t).toLinearMap) ∧
      T.derivative=(fun t => (cartesianPhysicalTestDerivative o δ hδ N ρ.value H τ η t).toLinearMap) ∧
      ∀ (t : ℝ) (z : CartesianPhysicalState δ hδ N),
        let σ := ((ρ.scaled η).multiplier w τ t).onSubdomain hdom.subset
        let r := cartesianReconstruction o δ hδ N
        let p := cartesianStateSeminorm o δ hδ N σ.value
        (p z)^2 ≤ Cmass*(σ.seminorm (r.RH z))^2 ∧
        (σ.seminorm (r.RH z))^2 ≤ Cmass*(p z)^2 ∧
        (σ.seminorm ((cartesianLoadInterface o δ hδ N).lift z))^2 ≤ Cmass*(p z)^2 ∧
        inner ℝ z (T.op t z) ≤ Cmass*(σ.seminorm (r.RH z))^2 ∧
        (σ.seminorm (r.RH z))^2 ≤ Cmass*inner ℝ z (T.op t z) ∧
        (z ≠ 0 → 0 < inner ℝ z (T.op t z)) ∧
        σ.observation ω₀ hω₀ (r.RH z) ≤
          Cobs*cartesianControlSeminorm o δ hδ N ω σ.value
            ((cartesianPhysicalControlExtension o δ hδ N ω).adjoint z) := by
  have hρ₁ := hρ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  obtain ⟨ε,hε,he1,Ctime,hCt,Csuper,hCs,htest⟩ :=
    cartesian_weightedTest_interface hS hc hcompact ρ hρ κ β τStar hκ hβ hτStar
  obtain ⟨Cmass,hCm,hmass⟩ := allowed_weight_cartesian_physical_stability hS hc hcompact ρ hρ₁
  obtain ⟨h₀,hh₀,Cobs,hCo,hobs⟩ := allowed_weight_cartesian_hilbert_observation
    hS hc hcompact ρ hρ₁ ω₀ ω hω₀ hcompact₀ hω hinc
  refine ⟨min ε h₀,lt_min hε hh₀,(min_le_left _ _).trans he1,
    Ctime,hCt,Csuper,hCs,Cmass,hCm,Cobs,hCo,?_⟩
  intro o δ hδ N hdom h hh hlower hupper w g H hsmall τ η hτ hη
  have hmε : h*w.max ≤ ε := hsmall.trans (min_le_left _ _)
  have hm1 : h*w.max ≤ 1 := hmε.trans he1
  have hh₀' : h ≤ h₀ := by
    have hmax : 1 ≤ w.max := (w.lower 0).trans (w.upper 0)
    have hp : h ≤ h*w.max := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hmax hh.le
    exact hp.trans (hsmall.trans (min_le_right _ _))
  have hqt (t : ℝ) : h*w.q t ≤ 1 := (mul_le_mul_of_nonneg_left (w.upper t) hh.le).trans hm1
  obtain ⟨T,hTop,hTder⟩ := htest o δ hδ N hdom h hh hlower hupper w g H τ η hτ hη hmε
  refine ⟨T,hTop,hTder,?_⟩
  intro t z
  dsimp only
  rw [hTop]
  have hm := hmass o δ hδ N hdom.subset h hh hupper w τ t η hη (hqt t) z
  have ho := hobs o δ hδ N hdom.subset h hh hh₀' hupper w τ t η hη (hqt t) z
  exact ⟨hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2,
    cartesianPhysicalTest_positive o δ hδ N ρ.value w τ η t z,ho⟩

end Carleman
