module

public import Carleman.Control.FullP1NumericalData
public import Carleman.Control.GalerkinHeatData
public import Carleman.Transfer.FiniteHalfspaceHeatContinuous
public import Carleman.Control.FullP1Realization
public import Carleman.Weights.DirichletAllowedData
public import Carleman.Spatial.ConformingUniformInverse
public import Carleman.Geometry.FiniteHalfspaceCharts

/-! The actual consistent-mass full P1 physical load estimate on the original bounded convex polytope. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open MeasureTheory Set
namespace Carleman.Physical
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem finite_halfspace_p1_physical_load_carleman {κidx : Type*} [Fintype κidx] (hdim : d+1 ≤ 3)
    (L : κidx → SpatialCoordinates (d+1) →L[ℝ] ℝ) (b : κidx → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<L i x})
    {ω : Set (SpatialCoordinates (d+1))} (hω : IsOpen ω) (hne : ω.Nonempty)
    (hωS : ω ⊆ {x | ∀ i, b i<L i x})
    (shape cmesh Bmesh γ : ℝ) (hshape : 0 < shape) (hcmesh : 0 < cmesh) (hBmesh : 0 < Bmesh)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit (d+1)) :
    let S := {x | ∀ i, b i<L i x}
    letI : IsFiniteMeasure (volume.restrict S) :=
      ⟨by simpa using hbounded.measure_lt_top (μ := volume)⟩
    let a := boundedDirichletOriginalForm (finite_halfspace_isOpen L b) (Nat.zero_lt_succ d)
      hbounded
    ∃ (c : SpatialCoordinates (d+1)) (l β qc κ h0 Δ0 C : ℝ), c ∈ ω ∧ ∃ hl : 1 ≤ l,
      0 < β ∧ β ≤ 1 ∧ 1 ≤ qc ∧ 0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < C ∧
      let ρ := interiorSpatialProfile (volume.restrict S) c (zero_le_one.trans hl)
      ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι),
        M.FaceMatching → M.BoundaryFitted →
      ∀ (centers : ι → SpatialCoordinates (d+1)) (r ℓ : ι → ℝ),
        (∀ i, 0 < r i) → (∀ i, Metric.ball (centers i) (r i) ⊆ M.cell i) →
        (∀ i, M.cellDiameter i ≤ shape*r i) → (∀ i, 0 < ℓ i) →
        (∀ i, cmesh*M.cellDiameter i ≤ ℓ i) → (∀ i, ℓ i ≤ Bmesh*M.cellDiameter i) →
        (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
        M.maxDiameter ≤ h0 →
      ∀ (g : TimeGrid) (w : TimeWeight), IntervalQClass w.q g.period β qc → g.dt ≤ Δ0 →
        w.max ≤ κ*min (M.maxDiameter^(-(4/5:ℝ))) (g.dt^(-(2/5:ℝ))) →
      let X := M.conformingSpace (dirichletSubspace S)
      let hX := M.conformingSpace_le (dirichletSubspace S)
      PhysicalLoadCarleman ρ w g (galerkinStiffness a X hX) X.subtype
        (conformingAmbientControl X ω hω.measurableSet).adjoint.toLinearMap
        X.orthogonalProjectionOnto.toLinearMap C := by
  let S := {x | ∀ i, b i<L i x}
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using hbounded.measure_lt_top (μ := volume)⟩
  dsimp only
  obtain ⟨c,l,β,qc,Cce,hc,hl,hβ,hβ1,hqc,hCce,_hphase,hce⟩ :=
    finite_halfspace_heat_continuous_data (Nat.zero_lt_succ d) L b hbounded hω hne hωS
  let hS := finite_halfspace_isOpen L b
  let hb := hbounded
  let a := boundedDirichletOriginalForm hS (Nat.zero_lt_succ d) hb
  let hD := finite_halfspace_dirichlet_domain_le_h2 (Nat.zero_lt_succ d) L b hbounded (hωS hc)
  let ρ := interiorSpatialProfile (volume.restrict S) c (zero_le_one.trans hl)
  have hρ : SmoothOnClosure ρ.value S := interiorCarlemanProfile_smoothOnClosure c l S
  have hρ2 : ContDiffOn ℝ 2 ρ.value (closure S) :=
    ((interiorCarlemanProfile_contDiff c l).of_le (by norm_num)).contDiffOn
  obtain ⟨Creg,hCr,hreg⟩ :=
    finite_halfspace_dirichlet_graph_estimate (Nat.zero_lt_succ d) L b hbounded (hωS hc)
  obtain ⟨Ca,Ccomm,hCa,hCc,hfamily⟩ := dirichlet_allowed_family_uniform hS (Nat.zero_lt_succ d) hb ρ hρ
  have hallowed := hfamily hD
  obtain ⟨ε,hε,_he1,Ctime,hCt,Csuper,hCs,Capp,hCap,hnum⟩ :=
    full_p1_numericalData (Nat.zero_lt_succ d) hdim hS (finite_halfspace_convex L b)
      hb.isCompact_closure ρ hρ2 shape cmesh Bmesh γ β 2 hshape hcmesh hBmesh hγ hΓ hβ
      (by norm_num) ω ω hω.measurableSet Subset.rfl
  have hcover : max (CarlemanExponents.heat.dStar/2) (CarlemanExponents.heat.bStar/2) ≤ 2 := by
    rw [CarlemanExponents.heat_scale_exponents.1,CarlemanExponents.heat_scale_exponents.2.1]
    norm_num
  obtain ⟨κ0,h0,Δ0,Cfinal,hκ0,hh0,hh01,hΔ0,hΔ01,hCf,htransfer⟩ :=
    conforming_heat_load_uniform (finite_halfspace_bounded_lipschitz L b c (hωS hc) hbounded) a hD ρ hρ
      heatDifferentialFamily ω hω.measurableSet Capp Creg (1/2) Ca Ccomm β 2 Ctime Csuper ε 1 Cce
      hCap.le (by norm_num) (zero_le_one.trans hCa) hCc.le hβ (by norm_num)
      hCt.le hCs.le hε (by norm_num) hCce.le hcover hreg
  let κ := min κ0 ε
  have hκ : 0 < κ := lt_min hκ0 hε
  refine ⟨c,l,β,qc,κ,h0,Δ0,Cfinal,hc,hl,hβ,hβ1,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCf,?_⟩
  intro ι _ M hM hBnd centers r ℓ hr hball hsh hℓ hlow hupp hg hmesh g w hq hdt hscale
  let X := M.conformingSpace (dirichletSubspace S)
  let hX := M.conformingSpace_le (dirichletSubspace S)
  have hm : 0 < M.maxDiameter := M.maxDiameter_pos (Nat.zero_lt_succ d) (hne.mono hωS)
  have hscale0 : w.max ≤ κ0*min (M.maxDiameter^(-(4/5:ℝ))) (g.dt^(-(2/5:ℝ))) :=
    hscale.trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (le_min (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg g.dt_pos.le _)))
  have hsx : w.max ≤ κ*M.maxDiameter^(-(4/5:ℝ)) := hscale.trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hκ.le)
  have hsmall : M.maxDiameter*w.max ≤ ε := by
    have hx := scale_monomial_le (p := (1:ℝ)) (ν := (1:ℝ)) hm (hmesh.trans hh01)
      (zero_le_one.trans w.max_ge_one) hκ.le (by norm_num) (by norm_num : (4/5:ℝ)*1 ≤ 1) hsx
    have hx' : M.maxDiameter*w.max ≤ κ := by simpa only [Real.rpow_one] using hx
    exact hx'.trans (min_le_right κ0 ε)
  obtain ⟨ND⟩ := hnum ι M hM hBnd centers r ℓ hr hball hsh hℓ hlow hupp hg hD w g hq.toRegularity hsmall
  let H : GalerkinHeatData a hD ρ heatDifferentialFamily ω hω.measurableSet X hX g w
      (1/2) Ca Ccomm 2 Ctime Csuper Cce M.maxDiameter
      (p1ErrorScales Capp M.maxDiameter hCap.le M.maxDiameter_nonneg) := {
    allowed := hallowed w 2
    approximation := ND.approximation
    test := ND.test
    continuous := hce X (Lp ℝ 2 (volume.restrict S)) (Lp ℝ 2 (volume.restrict S))
      (conformingWeightedState X ρ w) (fun t => (ρ.multiplier w 0 t).seminorm)
      (fun t => (ρ.multiplier w 0 t).seminorm) (conformingWeightedState_definite X ρ w)
      (fun t f => (ρ.seminorm_definite w 0 t f).mp)
      (fun t f => (ρ.seminorm_definite w 0 t f).mp) g w hq }
  exact htransfer X hX (galerkinStiffness a X hX) 0 g w hq.toRegularity M.maxDiameter
    (p1ErrorScales Capp M.maxDiameter hCap.le M.maxDiameter_nonneg) hm hmesh hdt hscale0
    (by simp only [p1ErrorScales,le_refl]) (by simp only [p1ErrorScales,add_zero,le_refl]) H.toConforming

end Carleman.Physical
