module
public import Carleman.Spatial.InnerGraphDensity
public import Carleman.Spatial.DomainHeatIntegral
public import Carleman.Spatial.IntervalHeatEnergies
public import Carleman.Spatial.WeakTrajectoryHeatEnergies
/-! Uniform estimates for every original weak periodic state on the actual smooth inner domains. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace Carleman
variable {d : ℕ}

theorem dirichletHeat_le_of_classical_of_dense {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
    (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (hq : AEStronglyMeasurable w.q g.timeMeasure)
    (ε C : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (hdense : Dense (classicalDirichletTimeCore hS hd hb g : Set
      ((boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g)))
    (hCE : ∀ p ∈ classicalDirichletTimeCore hS hd hb g,
      dirichletHeatLeft hS hd hb g ρ w p ≤ C*dirichletHeatRight hS hd hb g ρ w ε W hW p) :
    ∀ p, dirichletHeatLeft hS hd hb g ρ w p ≤ C*dirichletHeatRight hS hd hb g ρ w ε W hW p := by
  intro p
  have hc := isClosed_le (continuous_dirichletHeatLeft hS hd hb g ρ w hq)
    ((continuous_dirichletHeatRight hS hd hb g ρ w hq ε W hW).const_mul C)
  exact (closure_minimal hCE hc) (hdense p)

theorem halfspaceSmoothInner_uniform_weak_C2_heat_both_signs {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ n : ℕ, c ∈ halfspaceSmoothInner ℓ b n → ∀ (g : TimeGrid) (w : TimeWeight), ContDiffOn ℝ 2 w.q (Icc 0 g.period) →
      w.q 0=w.q g.period →
      derivWithin w.q (Icc 0 g.period) 0=derivWithin w.q (Icc 0 g.period) g.period →
      derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) 0=
        derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) g.period →
      (∀ t ∈ Icc 0 g.period, qc ≤ w.q t) →
      (∀ t ∈ Icc 0 g.period, |derivWithin w.q (Icc 0 g.period) t| ≤ β*(w.q t)^2) →
      (∀ t ∈ Icc 0 g.period,
        |derivWithin (derivWithin w.q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(w.q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      let ρ := interiorSpatialProfile (volume.restrict (halfspaceSmoothInner ℓ b n)) c (zero_le_one.trans hl)
      ∀ p : (boundedDirichletOriginalForm (halfspaceSmoothInner_open ℓ b n) hd
          ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure)).model.PeriodicGraph g,
        dirichletHeatLeft (halfspaceSmoothInner_open ℓ b n) hd
          ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure) g ρ w p ≤
        C*dirichletHeatRight (halfspaceSmoothInner_open ℓ b n) hd
          ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure) g ρ w ε W hW.measurableSet p := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hsmooth⟩ :=
    halfspaceSmoothInner_uniform_interval_C2_heat_both_signs ℓ b hbounded hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro n hcn g w hq he0 he1 he2 hqmin hq1 hq2 ε hε
  let ρ := interiorSpatialProfile (volume.restrict (halfspaceSmoothInner ℓ b n)) c (zero_le_one.trans hl)
  have hm : AEStronglyMeasurable w.q g.timeMeasure := by
    simpa only [TimeGrid.timeMeasure,restrict_Ioo_eq_restrict_Icc] using
      hq.continuousOn.aestronglyMeasurable measurableSet_Icc
  apply dirichletHeat_le_of_classical_of_dense (halfspaceSmoothInner_open ℓ b n) hd
    ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure)
    g ρ w hm ε C W hW.measurableSet
    (halfspaceSmoothInner_classicalTimeCore_dense hd ℓ b n hbounded hcn g)
  intro p hp
  obtain ⟨F,hF,hFp,hFb,hFt,hFd⟩ := hp
  have hleft := dirichletHeatLeft_eq_domainIntegral (halfspaceSmoothInner ℓ b n) (halfspaceSmoothInner_open ℓ b n) hd ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure) g ρ w
    hq.continuousOn (interiorCarlemanProfile_contDiff c l).continuous p hF hFt
  have hright := dirichletHeatRight_eq_domainIntegral (halfspaceSmoothInner ℓ b n) (halfspaceSmoothInner_open ℓ b n) hd ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure) g ρ w
    hq.continuousOn (interiorCarlemanProfile_contDiff c l).continuous p hF hFt ε W hW.measurableSet hFd
  rw [hleft,hright]
  have hh := hsmooth n hcn g.period g.period_pos w.q hq he0 he1 he2 hqmin hq1 hq2 ε hε F hF hFp hFb
  simpa only [ρ,interiorSpatialProfile,interiorGaussianHeatPhase,separableHeatPhase,mul_comm] using hh


theorem halfspaceSmoothInner_uniform_weak_interval_C2_heat_both_signs {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ n : ℕ, c ∈ halfspaceSmoothInner ℓ b n → ∀ (g : TimeGrid) (q : ℝ → ℝ), ContDiffOn ℝ 2 q (Icc 0 g.period) →
      q 0=q g.period →
      derivWithin q (Icc 0 g.period) 0=derivWithin q (Icc 0 g.period) g.period →
      derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) 0=
        derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) g.period →
      (∀ t ∈ Icc 0 g.period, qc ≤ q t) →
      (∀ t ∈ Icc 0 g.period, |derivWithin q (Icc 0 g.period) t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 g.period,
        |derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      let ρ := interiorSpatialProfile (volume.restrict (halfspaceSmoothInner ℓ b n)) c (zero_le_one.trans hl)
      ∀ p : (boundedDirichletOriginalForm (halfspaceSmoothInner_open ℓ b n) hd
          ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure)).model.PeriodicGraph g,
        dirichletIntervalHeatLeft (halfspaceSmoothInner_open ℓ b n) hd
          ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure) g ρ q p ≤
        C*dirichletIntervalHeatRight (halfspaceSmoothInner_open ℓ b n) hd
          ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure) g ρ q ε W hW.measurableSet p := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hweak⟩ :=
    halfspaceSmoothInner_uniform_weak_C2_heat_both_signs hd ℓ b hbounded hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro n hcn g q hq he0 he1 he2 hqmin hq1 hq2 ε hε
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
  let ρ := interiorSpatialProfile (volume.restrict (halfspaceSmoothInner ℓ b n)) c (zero_le_one.trans hl)
  intro p
  have hh := hweak n hcn g w (hq.congr he) hw0 hw1 hw2 hwmin hwd1 hwd2 ε hε p
  change dirichletHeatLeft (halfspaceSmoothInner_open ℓ b n) hd
    ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure) g ρ w p ≤
    C*dirichletHeatRight (halfspaceSmoothInner_open ℓ b n) hd
      ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure) g ρ w ε W hW.measurableSet p at hh
  rw [dirichletHeatLeft_eq_interval _ _ _ _ _ q w he,
    dirichletHeatRight_eq_interval _ _ _ _ _ q w he] at hh
  exact hh


theorem halfspaceSmoothInner_uniform_original_weak_C2_heat_both_signs {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWS : W ⊆ {x | ∀ i, b i<ℓ i x}) :
    ∃ (c : SpatialCoordinates d) (l β qc C : ℝ), c ∈ W ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < C ∧
      (∀ x, -2 < interiorCarlemanProfile c l x ∧ interiorCarlemanProfile c l x ≤ -1) ∧
      ∀ n : ℕ, c ∈ halfspaceSmoothInner ℓ b n → ∀ (g : TimeGrid) (q : ℝ → ℝ), ContDiffOn ℝ 2 q (Icc 0 g.period) →
      q 0=q g.period →
      derivWithin q (Icc 0 g.period) 0=derivWithin q (Icc 0 g.period) g.period →
      derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) 0=
        derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) g.period →
      (∀ t ∈ Icc 0 g.period, qc ≤ q t) →
      (∀ t ∈ Icc 0 g.period, |derivWithin q (Icc 0 g.period) t| ≤ β*(q t)^2) →
      (∀ t ∈ Icc 0 g.period,
        |derivWithin (derivWithin q (Icc 0 g.period)) (Icc 0 g.period) t| ≤ β^2*(q t)^3) →
      ∀ ε : ℝ, (ε=1 ∨ ε=-1) →
      let B := (boundedDirichletOriginalForm (halfspaceSmoothInner_open ℓ b n) hd
        ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure)).model
      let ρ := interiorSpatialProfile (volume.restrict (halfspaceSmoothInner ℓ b n)) c (zero_le_one.trans hl)
      ∀ u : PeriodicWeakTrajectory g B.domain B.operator,
        timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm) u.value+
          timeSq g q 1 (fun t => (ρ.expMultiplier (q t)).seminorm)
            (fun t => WeakSobolevJet.field 1 (dirichletDomainJet (halfspaceSmoothInner_open ℓ b n)
              hd ((halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure) (u.domainValue t))) ≤
        C*(timeSq g q 0 (fun t => (ρ.expMultiplier (q t)).seminorm)
            (fun t => ε • u.derivative t+B.operator (u.domainValue t))+
          timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm)
            (fun t => (BoundedMultiplier.cutoff W hW.measurableSet).map (u.value t))) := by
  obtain ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,hweak⟩ :=
    halfspaceSmoothInner_uniform_weak_interval_C2_heat_both_signs hd ℓ b hbounded hW hne hWS
  refine ⟨c,l,β,qc,C,hc,hl,hβ,hβ1,hqc,hC,hρ,?_⟩
  intro n hcn g q hq he0 he1 he2 hqmin hq1 hq2 ε hε
  dsimp only
  intro u
  have hh := hweak n hcn g q hq he0 he1 he2 hqmin hq1 hq2 ε hε u.toPeriodicGraph
  rw [dirichletIntervalHeatLeft_trajectory,dirichletIntervalHeatRight_trajectory] at hh
  exact hh


end Carleman
