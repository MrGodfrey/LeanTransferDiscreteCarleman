module

public import Carleman.Control.ConformingRegionWeightedData
public import Carleman.Control.FullP1WeightedTest
public import Carleman.Spatial.FullP1ApproximationInterface
public import Carleman.Spatial.DirichletForm

/-! Actual consistent-mass P1 N1--N5 data with the original L²(omega)
control space, full Dirichlet P1 state space, and h/h² error scales.
The continuous H² domain inclusion remains exactly the original A1 input. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2400000
open MeasureTheory Set
namespace Carleman
attribute [local instance] Classical.propDecidable

def p1ErrorScales (C h : ℝ) (hC : 0 ≤ C) (hh : 0 ≤ h) : ErrorScales where
  aE := C*h
  a₀ := C*h^2
  ηA := 0
  aE_nonneg := mul_nonneg hC hh
  a₀_nonneg := mul_nonneg hC (sq_nonneg h)
  ηA_nonneg := le_rfl

theorem full_p1_numericalData {d : ℕ} (hdpos : 0 < d) (hdim : d ≤ 3)
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 2 ρ.value (closure S))
    (κ c B γ β τStar : ℝ) (hκ : 0 < κ) (hcpos : 0 < c) (hBpos : 0 < B)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (ω₀ ω : Set (SpatialCoordinates d)) (hω₀ : MeasurableSet ω₀) (hinc : ω₀ ⊆ ω) :
    letI : IsFiniteMeasure (volume.restrict S) :=
      ⟨by simpa using (hcompact.isBounded.subset subset_closure).measure_lt_top (μ := volume)⟩
    let a := boundedDirichletOriginalForm hS hdpos (hcompact.isBounded.subset subset_closure)
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ ∃ Ctime > (0:ℝ), ∃ Csuper > (0:ℝ),
      ∃ (Capp : ℝ) (hCa : 0 < Capp),
    ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι),
      M.FaceMatching → M.BoundaryFitted →
    ∀ (centers : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (centers i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, 0 < ℓ i) →
      (∀ i, c*M.cellDiameter i ≤ ℓ i) → (∀ i, ℓ i ≤ B*M.cellDiameter i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (hD : a.model.domain ≤ sobolevSubspace d (2*1) (volume.restrict S) S)
      (w : TimeWeight) (g : TimeGrid) (_H : TimeWeightRegularity w g β), M.maxDiameter*w.max ≤ δ →
    let X := M.conformingSpace (dirichletSubspace S)
    let hX := M.conformingSpace_le (dirichletSubspace S)
    Nonempty (Section5.NumericalData a hD (Physical.conformingReconstruction (dirichletSubspace S) X hX)
      (Physical.galerkinStiffness a X hX).toLinearMap 0 (Physical.conformingLoad (dirichletSubspace S) X hX)
      (Physical.conformingRegionControl X ω).adjoint.toLinearMap g w ρ ω₀ hω₀
      (Physical.conformingWeightedState X ρ w) (fun t => (ρ.multiplier w 0 t).seminorm)
      (fun t => ((ρ.multiplier w 0 t).restrictMeasure Measure.restrict_le_self).seminorm)
      τStar Ctime Csuper 1 M.maxDiameter (p1ErrorScales Capp M.maxDiameter hCa.le M.maxDiameter_nonneg)) := by
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using (hcompact.isBounded.subset subset_closure).measure_lt_top (μ := volume)⟩
  let a := boundedDirichletOriginalForm hS hdpos (hcompact.isBounded.subset subset_closure)
  have hρ₁ := hρ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  obtain ⟨δₜ,hδₜ,ht1,Ctime,hCt,Csuper,hCs,htest⟩ := full_p1_weightedTest_interface hS hc hcompact ρ hρ
    κ c B γ β τStar hκ hcpos hBpos hγ hΓ hβ hτStar
  obtain ⟨δₐ,hδₐ,_,Capp,hCa,happrox⟩ := full_p1_weightedApproximation_interface hdim hS hc hcompact ρ hρ₁
    κ c B γ hκ hcpos hBpos hγ hΓ
  refine ⟨min δₜ δₐ,lt_min hδₜ hδₐ,(min_le_left _ _).trans ht1,Ctime,hCt,Csuper,hCs,Capp,hCa,?_⟩
  intro ι _ M hM hBnd centers r ℓ hr hball hshape hℓ hlow hupp hg hD w g H hm
  let X := M.conformingSpace (dirichletSubspace S)
  let hX := M.conformingSpace_le (dirichletSubspace S)
  have hsigned (e : Bool) : ∃ η : ℝ, |η|=1 ∧ ρ.scaled η=ρ.signed e := by
    cases e
    · exact ⟨1,abs_one,ρ.scaled_one⟩
    · exact ⟨-1,by norm_num,ρ.scaled_neg_one⟩
  refine ⟨Physical.galerkinRegionNumericalData a hD X hX ρ ω₀ ω hω₀ hinc g w τStar Ctime Csuper
    M.maxDiameter (p1ErrorScales Capp M.maxDiameter hCa.le M.maxDiameter_nonneg) ?_ ?_⟩
  · intro e τ _
    obtain ⟨η,hη,he⟩ := hsigned e
    rw [← he]
    exact happrox ι M hM hBnd centers r ℓ hr hball hshape hℓ hlow hupp hg a.model.domain hD a.domain_le
      w g τ η hη (hm.trans (min_le_right _ _))
  · intro e τ hτ
    let η := Classical.choose (hsigned e)
    have hη := (Classical.choose_spec (hsigned e)).1
    have he := (Classical.choose_spec (hsigned e)).2
    rw [← he]
    exact Classical.choose (htest M hM hBnd centers r ℓ hr hball hshape hℓ hlow hupp hg w
      (hm.trans (min_le_left _ _)) g H τ η hτ hη)

end Carleman
