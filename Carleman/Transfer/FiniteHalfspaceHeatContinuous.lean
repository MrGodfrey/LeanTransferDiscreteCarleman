module

public import Carleman.Transfer.DirichletHeatGeometry
public import Carleman.Spatial.FiniteHalfspaceWeakHeat
public import Carleman.Weights.IntervalQClass

/-! The finite-halfspace theorem discharges the actual continuous hypothesis of the original transfer interface. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set
universe u v y
namespace Carleman
variable {d : ℕ}

theorem finite_halfspace_heat_continuous_data {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      let B := boundedDirichletOriginalForm (finite_halfspace_isOpen ℓ b) hd
        hb
      let ρ := interiorSpatialProfile (volume.restrict ({x | ∀ i, b i<ℓ i x})) c (zero_le_one.trans hl)
      ∀ (X : Type u) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
        (F : Type v) [AddCommGroup F] [Module ℝ F]
        (Y : Type y) [AddCommGroup Y] [Module ℝ Y]
        (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
        (hstate : ∀ t z, state t z = 0 → z = 0)
        (hload : ∀ t z, load t z = 0 → z = 0)
        (hcontrol : ∀ t z, control t z = 0 → z = 0)
        (g : TimeGrid) (w : TimeWeight), IntervalQClass w.q g.period β qc →
      let p := sobolevGeometry (a := CarlemanExponents.heat) (finite_halfspace_isOpen ℓ b)
        (ae_restrict_mem (finite_halfspace_isOpen ℓ b).measurableSet) B.sobolev w ρ
        heatDifferentialFamily W hW.measurableSet state load control hstate hload hcontrol
      ∀ (s : Orientation) (U : PeriodicWeakTrajectory g B.model.domain B.model.operator),
        p.continuousEnergy g (p.trajectory g B.domain_le U) ≤ C *
          (timeSq g w.q 0 p.space (fun t => s.sign • U.derivative t+B.model.operator (U.domainValue t))+
            timeSq g w.q CarlemanExponents.heat.o p.observation
              (fun t => (U.domainValue t : Lp ℝ 2 (volume.restrict ({x | ∀ i, b i<ℓ i x}))))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hce⟩ :=
    finite_halfspace_original_weak_C2_heat_both_signs hd ℓ b hb hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  dsimp only
  intro X _ _ F _ _ Y _ _ state load control hstate hload hcontrol g w hq s U
  let ρ := interiorSpatialProfile (volume.restrict ({x | ∀ i, b i<ℓ i x})) c (zero_le_one.trans hl)
  have hL := dirichletHeatGeometry_energy (finite_halfspace_isOpen ℓ b)
    hd hb w ρ W hW.measurableSet
    state load control hstate hload hcontrol g U
  have hR := dirichletHeatGeometry_residual (finite_halfspace_isOpen ℓ b)
    hd hb w ρ W hW.measurableSet
    state load control hstate hload hcontrol g s.sign U
  have hO := dirichletHeatGeometry_observation (finite_halfspace_isOpen ℓ b)
    hd hb w ρ W hW.measurableSet
    state load control hstate hload hcontrol g U
  have hh := hce g w.q hq.smooth hq.endpoint hq.first_endpoint hq.second_endpoint hq.lower
    hq.first_bound hq.second_bound s.sign (by cases s <;> simp [Orientation.sign]) U
  exact hL.trans_le (hh.trans_eq (congrArg (fun z : ℝ => C*z)
    (congrArg₂ (fun x y : ℝ => x+y) hR hO).symm))

end Carleman
