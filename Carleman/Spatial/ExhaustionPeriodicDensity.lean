module
public import Carleman.Spatial.HarmonicDomainLimit
public import Carleman.Continuous.HarmonicStateDensity
/-! A dense subspace of original periodic states approximable by genuine inner periodic states. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
  (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
  (T : ℕ → Set (SpatialCoordinates d)) (hT : ∀ n, IsOpen (T n)) (hTS : ∀ n, T n⊆S)
  (g : TimeGrid)

def dirichletExhaustionApproximable :
    Submodule ℝ ((boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) where
  carrier p := ∃ P : ∀ n, (boundedDirichletOriginalForm (hT n) hd (hb.subset (hTS n))).model.PeriodicGraph g,
    Tendsto (fun n => subdomainHeatFields S (T n) g
      (dirichletHeatFields (hT n) hd (hb.subset (hTS n)) g (P n))) atTop
      (𝓝 (dirichletHeatFields hS hd hb g p))
  zero_mem' := by
    refine ⟨fun _ => 0,?_⟩
    simpa only [ContinuousLinearMap.map_zero] using
      (tendsto_const_nhds (x := (0 : DirichletHeatFields S g)) (f := (atTop : Filter ℕ)))
  add_mem' := by
    rintro p q ⟨P,hP⟩ ⟨Q,hQ⟩
    refine ⟨fun n => P n+Q n,?_⟩
    simpa only [ContinuousLinearMap.map_add] using hP.add hQ
  smul_mem' := by
    rintro c p ⟨P,hP⟩
    refine ⟨fun n => c • P n,?_⟩
    simpa only [ContinuousLinearMap.map_smul] using hP.const_smul c

theorem dirichletExhaustionApproximable_dense (hm : Monotone T) (hcover : S⊆⋃ n,T n) :
    Dense (dirichletExhaustionApproximable hS hd hb T hT hTS g : Set
      ((boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g)) := by
  let B := (boundedDirichletOriginalForm hS hd hb).model
  apply (B.harmonicStateSpan_dense g).mono
  apply Submodule.span_le.mpr
  rintro p ⟨j,x,y,rfl⟩
  exact exists_dirichlet_exhaustion_harmonic_field_approximation hS hd hb T hT hTS hm hcover g j x y

end Carleman
