module
public import Carleman.Spatial.ExhaustionHeatTransfer
public import Carleman.Spatial.UniformInnerWeakHeat
/-! Uniform heat Carleman estimates on the original finite-halfspace domain. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace Carleman
variable {d : ℕ}

theorem finite_halfspace_weak_C2_heat_both_signs {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ (g : TimeGrid) (w : TimeWeight), ContDiffOn ℝ 2 w.q (Icc 0 g.period) →
      w.q 0=w.q g.period →
      derivWithin w.q (Icc 0 g.period) 0=derivWithin w.q (Icc 0 g.period) g.period →
      derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) 0=
        derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) g.period →
      (∀ t ∈ Icc 0 g.period, qc ≤ w.q t) →
      (∀ t ∈ Icc 0 g.period, |derivWithin w.q (Icc 0 g.period) t| ≤ β*(w.q t)^2) →
      (∀ t ∈ Icc 0 g.period,
        |derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(w.q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      let ρ := interiorSpatialProfile (volume.restrict {x | ∀ i, b i<ℓ i x}) c (zero_le_one.trans hl)
      ∀ p : (boundedDirichletOriginalForm (finite_halfspace_isOpen ℓ b) hd
          hbounded).model.PeriodicGraph g,
        dirichletHeatLeft (finite_halfspace_isOpen ℓ b) hd
          hbounded g ρ w p ≤
        C*dirichletHeatRight (finite_halfspace_isOpen ℓ b) hd
          hbounded g ρ w ε W hW.measurableSet p := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hweak⟩ :=
    halfspaceSmoothInner_uniform_weak_C2_heat_both_signs hd ℓ b hbounded hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro g w hq he0 he1 he2 hqmin hq1 hq2 ε hε
  let S := {x | ∀ i, b i<ℓ i x}
  let hS := finite_halfspace_isOpen ℓ b
  obtain ⟨N,hN⟩ := (halfspaceSmoothInner_eventually_mem ℓ b (hWS hc)).exists
  let T (n : ℕ) := halfspaceSmoothInner ℓ b (N+n)
  have hT (n : ℕ) : IsOpen (T n) := halfspaceSmoothInner_open ℓ b (N+n)
  have hTS (n : ℕ) : T n⊆S := subset_closure.trans (halfspaceSmoothInner_closure_subset ℓ b (N+n))
  have hcT (n : ℕ) : c∈T n := halfspaceSmoothInner_mono ℓ b (Nat.le_add_right N n) hN
  have hm : Monotone T := fun n m hnm => halfspaceSmoothInner_mono ℓ b (Nat.add_le_add_left hnm N)
  have hcover : S⊆⋃ n, T n := by
    intro x hx
    obtain ⟨n,hn⟩ := (halfspaceSmoothInner_eventually_mem ℓ b hx).exists
    exact mem_iUnion.mpr ⟨n,halfspaceSmoothInner_mono ℓ b (Nat.le_add_left n N) hn⟩
  let ρ := interiorSpatialProfile (volume.restrict S) c (zero_le_one.trans hl)
  let ρn (n : ℕ) := interiorSpatialProfile (volume.restrict (T n)) c (zero_le_one.trans hl)
  have hρn (n : ℕ) : ρ.value=ᵐ[volume.restrict (T n)] (ρn n).value := Eventually.of_forall fun _ => rfl
  have hqm : AEStronglyMeasurable w.q g.timeMeasure := by
    simpa only [TimeGrid.timeMeasure,restrict_Ioo_eq_restrict_Icc] using
      hq.continuousOn.aestronglyMeasurable measurableSet_Icc
  apply dirichletHeat_le_of_exhaustion hS hd hbounded T hT hTS hm hcover g ρ ρn hρn w hqm ε C W hW.measurableSet
  intro n p
  exact hweak (N+n) (hcT n) g w hq he0 he1 he2 hqmin hq1 hq2 ε hε p


theorem finite_halfspace_weak_interval_C2_heat_both_signs {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ (g : TimeGrid) (q : ℝ → ℝ), ContDiffOn ℝ 2 q (Icc 0 g.period) →
      q 0=q g.period →
      derivWithin q (Icc 0 g.period) 0=derivWithin q (Icc 0 g.period) g.period →
      derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) 0=
        derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) g.period →
      (∀ t ∈ Icc 0 g.period, qc ≤ q t) →
      (∀ t ∈ Icc 0 g.period, |derivWithin q (Icc 0 g.period) t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 g.period,
        |derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      let ρ := interiorSpatialProfile (volume.restrict {x | ∀ i, b i<ℓ i x}) c (zero_le_one.trans hl)
      ∀ p : (boundedDirichletOriginalForm (finite_halfspace_isOpen ℓ b) hd
          hbounded).model.PeriodicGraph g,
        dirichletIntervalHeatLeft (finite_halfspace_isOpen ℓ b) hd
          hbounded g ρ q p ≤
        C*dirichletIntervalHeatRight (finite_halfspace_isOpen ℓ b) hd
          hbounded g ρ q ε W hW.measurableSet p := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hweak⟩ :=
    finite_halfspace_weak_C2_heat_both_signs hd ℓ b hbounded hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro g q hq he0 he1 he2 hqmin hq1 hq2 ε hε
  dsimp only
  obtain ⟨w,_hwcont,he⟩ := exists_timeWeight_eqOn_interval g hq.continuousOn
    (fun t ht => hqc.trans (hqmin t ht))
  have heD := eqOn_interval_within_derivatives he
  have h0 : (0:ℝ) ∈ Icc 0 g.period := ⟨le_rfl,g.period_pos.le⟩
  have hT : g.period ∈ Icc 0 g.period := ⟨g.period_pos.le,le_rfl⟩
  have hw0 : w.q 0=w.q g.period := by rw [he h0,he hT,he0]
  have hw1 : derivWithin w.q (Icc 0 g.period) 0=derivWithin w.q (Icc 0 g.period) g.period := by
    rw [(heD 0 h0).2.1,(heD g.period hT).2.1,he1]
  have hw2 : derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) 0=
      derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) g.period := by
    rw [(heD 0 h0).2.2,(heD g.period hT).2.2,he2]
  have hwmin : ∀ t ∈ Icc 0 g.period, qc ≤ w.q t := fun t ht => by rw [he ht]; exact hqmin t ht
  have hwd1 : ∀ t ∈ Icc 0 g.period, |derivWithin w.q (Icc 0 g.period) t| ≤ β*(w.q t)^2 := by
    intro t ht
    rw [(heD t ht).2.1,he ht]
    exact hq1 t ht
  have hwd2 : ∀ t ∈ Icc 0 g.period,
      |derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(w.q t)^3 := by
    intro t ht
    rw [(heD t ht).2.2,he ht]
    exact hq2 t ht
  let ρ := interiorSpatialProfile (volume.restrict {x | ∀ i, b i<ℓ i x}) c (zero_le_one.trans hl)
  intro p
  have hh := hweak g w (hq.congr he) hw0 hw1 hw2 hwmin hwd1 hwd2 ε hε p
  change dirichletHeatLeft (finite_halfspace_isOpen ℓ b) hd
    hbounded g ρ w p ≤
    C*dirichletHeatRight (finite_halfspace_isOpen ℓ b) hd
      hbounded g ρ w ε W hW.measurableSet p at hh
  rw [dirichletHeatLeft_eq_interval _ _ _ _ _ q w he,
    dirichletHeatRight_eq_interval _ _ _ _ _ q w he] at hh
  exact hh


theorem finite_halfspace_original_weak_C2_heat_both_signs {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ (g : TimeGrid) (q : ℝ → ℝ), ContDiffOn ℝ 2 q (Icc 0 g.period) →
      q 0=q g.period →
      derivWithin q (Icc 0 g.period) 0=derivWithin q (Icc 0 g.period) g.period →
      derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) 0=
        derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) g.period →
      (∀ t ∈ Icc 0 g.period, qc ≤ q t) →
      (∀ t ∈ Icc 0 g.period, |derivWithin q (Icc 0 g.period) t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 g.period,
        |derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      let B := (boundedDirichletOriginalForm (finite_halfspace_isOpen ℓ b) hd
        hbounded).model
      let ρ := interiorSpatialProfile (volume.restrict {x | ∀ i, b i<ℓ i x}) c (zero_le_one.trans hl)
      ∀ u : PeriodicWeakTrajectory g B.domain B.operator,
        timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm) u.value+
          timeSq g q 1 (fun t => (ρ.expMultiplier (q t)).seminorm)
            (fun t => WeakSobolevJet.field 1 (dirichletDomainJet (finite_halfspace_isOpen ℓ b)
              hd hbounded (u.domainValue t))) ≤
        C*(timeSq g q 0 (fun t => (ρ.expMultiplier (q t)).seminorm)
            (fun t => ε • u.derivative t+B.operator (u.domainValue t))+
          timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm)
            (fun t => (BoundedMultiplier.cutoff W hW.measurableSet).map (u.value t))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hweak⟩ :=
    finite_halfspace_weak_interval_C2_heat_both_signs hd ℓ b hbounded hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro g q hq he0 he1 he2 hqmin hq1 hq2 ε hε
  dsimp only
  intro u
  have hh := hweak g q hq he0 he1 he2 hqmin hq1 hq2 ε hε u.toPeriodicGraph
  rw [dirichletIntervalHeatLeft_trajectory,dirichletIntervalHeatRight_trajectory] at hh
  exact hh


end Carleman
