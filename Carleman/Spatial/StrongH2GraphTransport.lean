module
public import Carleman.Spatial.GraphShearHessianTransport
public import Carleman.Spatial.SpatialTestAllOrders
public import Mathlib.Analysis.Normed.Operator.Banach
/-! Actual graph pullback is continuous in the full H² graph topology.
Closed graph is used only for this fixed map, after genuine H² preservation. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
namespace WeakSobolevJet
variable {d m n : ℕ} {S T : Set (SpatialCoordinates d)}

def valueLiftLinear (hT : IsOpen T)
    (P : Lp ℝ 2 (volume.restrict S) →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u : WeakSobolevJet d m (volume.restrict S) S,
      ∃ v : WeakSobolevJet d n (volume.restrict T) T, value v=P (value u)) :
    WeakSobolevJet d m (volume.restrict S) S →ₗ[ℝ] WeakSobolevJet d n (volume.restrict T) T where
  toFun u := (hl u).choose
  map_add' u v := by
    apply value_injective hT (ae_restrict_mem hT.measurableSet)
    change value ((hl (u+v)).choose)=value ((hl u).choose+(hl v).choose)
    calc
      _ = P (value (u+v)) := (hl (u+v)).choose_spec
      _ = P (value u)+P (value v) := by rw [map_add,map_add]
      _ = _ := by rw [map_add,(hl u).choose_spec,(hl v).choose_spec]
  map_smul' c u := by
    apply value_injective hT (ae_restrict_mem hT.measurableSet)
    change value ((hl (c • u)).choose)=value (c • (hl u).choose)
    calc
      _ = P (value (c • u)) := (hl (c • u)).choose_spec
      _ = c • P (value u) := by rw [map_smul,map_smul]
      _ = _ := by rw [map_smul,(hl u).choose_spec]

theorem valueLiftLinear_value (hT : IsOpen T)
    (P : Lp ℝ 2 (volume.restrict S) →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u : WeakSobolevJet d m (volume.restrict S) S,
      ∃ v : WeakSobolevJet d n (volume.restrict T) T, value v=P (value u))
    (u : WeakSobolevJet d m (volume.restrict S) S) : value (valueLiftLinear hT P hl u)=P (value u) :=
  (hl u).choose_spec

theorem valueLiftLinear_closedGraph (hT : IsOpen T)
    (P : Lp ℝ 2 (volume.restrict S) →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u : WeakSobolevJet d m (volume.restrict S) S,
      ∃ v : WeakSobolevJet d n (volume.restrict T) T, value v=P (value u)) :
    IsClosed ((valueLiftLinear hT P hl).graph : Set
      (WeakSobolevJet d m (volume.restrict S) S × WeakSobolevJet d n (volume.restrict T) T)) := by
  have he : ((valueLiftLinear hT P hl).graph : Set
      (WeakSobolevJet d m (volume.restrict S) S × WeakSobolevJet d n (volume.restrict T) T))=
      {p | value p.2=P (value p.1)} := by
    ext ⟨u,v⟩
    change v=valueLiftLinear hT P hl u ↔ value v=P (value u)
    constructor
    · rintro rfl
      exact valueLiftLinear_value hT P hl u
    · intro hv
      apply value_injective hT (ae_restrict_mem hT.measurableSet)
      rw [valueLiftLinear_value,hv]
  rw [he]
  exact isClosed_eq (valueCLM.continuous.comp continuous_snd)
    (P.continuous.comp (valueCLM.continuous.comp continuous_fst))

def valueLiftCLM (hT : IsOpen T)
    (P : Lp ℝ 2 (volume.restrict S) →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u : WeakSobolevJet d m (volume.restrict S) S,
      ∃ v : WeakSobolevJet d n (volume.restrict T) T, value v=P (value u)) :
    WeakSobolevJet d m (volume.restrict S) S →L[ℝ] WeakSobolevJet d n (volume.restrict T) T :=
  ContinuousLinearMap.ofIsClosedGraph (valueLiftLinear_closedGraph hT P hl)

theorem valueLiftCLM_value (hT : IsOpen T)
    (P : Lp ℝ 2 (volume.restrict S) →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u : WeakSobolevJet d m (volume.restrict S) S,
      ∃ v : WeakSobolevJet d n (volume.restrict T) T, value v=P (value u))
    (u : WeakSobolevJet d m (volume.restrict S) S) : value (valueLiftCLM hT P hl u)=P (value u) :=
  valueLiftLinear_value hT P hl u

theorem valueLiftCLM_unique (hT : IsOpen T)
    (P : Lp ℝ 2 (volume.restrict S) →L[ℝ] Lp ℝ 2 (volume.restrict T))
    (hl : ∀ u : WeakSobolevJet d m (volume.restrict S) S,
      ∃ v : WeakSobolevJet d n (volume.restrict T) T, value v=P (value u))
    (u : WeakSobolevJet d m (volume.restrict S) S) (v : WeakSobolevJet d n (volume.restrict T) T)
    (hv : value v=P (value u)) : valueLiftCLM hT P hl u=v := by
  apply value_injective hT (ae_restrict_mem hT.measurableSet)
  rw [valueLiftCLM_value,hv]

variable (hT : IsOpen T) (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
  {C : NNReal} (hC : LipschitzWith C ψ)
  (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
  {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)

include hT hC hB in
theorem graphShear_H2_value_exists (U : WeakSobolevJet d 2 (volume.restrict T) T) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    ∃ V : WeakSobolevJet d 2 (volume.restrict (F ⁻¹' T)) (F ⁻¹' T),
      value V=homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T) (value U) := by
  obtain ⟨V,hV,_⟩ := exists_graphShearPullback_H2 hT r ψ hψ hC htrans hB U
  refine ⟨V,?_⟩
  have hv := congrArg value hV
  rw [truncate_value,graphShearPullback_value,truncate_value] at hv
  exact hv

def graphShearH2Pullback : WeakSobolevJet d 2 (volume.restrict T) T →L[ℝ]
    WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T) :=
  valueLiftCLM (hT.preimage (spatialGraphShear r ψ hψ.continuous htrans).continuous)
    (homeomorphPullbackLp (spatialGraphShear r ψ hψ.continuous htrans)
      (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)).toContinuousLinearMap
    (graphShear_H2_value_exists hT r ψ hψ hC htrans hB)

theorem graphShearH2Pullback_value (U : WeakSobolevJet d 2 (volume.restrict T) T) :
    value (graphShearH2Pullback hT r ψ hψ hC htrans hB U)=
      homeomorphPullbackLp (spatialGraphShear r ψ hψ.continuous htrans)
        (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T) (value U) :=
  valueLiftCLM_value _ _ _ U

theorem graphShearH2Pullback_ae (U : WeakSobolevJet d 2 (volume.restrict T) T) :
    value (graphShearH2Pullback hT r ψ hψ hC htrans hB U) =ᵐ[volume.restrict
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T)]
      value U ∘ spatialGraphShear r ψ hψ.continuous htrans := by
  rw [graphShearH2Pullback_value]
  exact homeomorphPullbackLp_ae _ _ _

theorem graphShearH2Pullback_truncate (U : WeakSobolevJet d 2 (volume.restrict T) T) :
    truncate (by decide : 1≤2) (graphShearH2Pullback hT r ψ hψ hC htrans hB U)=
      graphShearPullback hT r ψ hψ hC htrans (truncate (by decide : 1≤2) U) := by
  have hS := hT.preimage (spatialGraphShear r ψ hψ.continuous htrans).continuous
  apply value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [truncate_value,graphShearH2Pullback_value,graphShearPullback_value,truncate_value]

theorem graphShearH2Pullback_dirichlet (U : WeakSobolevJet d 2 (volume.restrict T) T)
    (hU : truncate (by decide : 1≤2) U∈dirichletJetSpace T) :
    truncate (by decide : 1≤2) (graphShearH2Pullback hT r ψ hψ hC htrans hB U)∈
      dirichletJetSpace (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T) := by
  rw [graphShearH2Pullback_truncate]
  exact graphShearPullback_dirichlet hT r ψ hψ hC htrans _ hU

theorem graphShearH2Pullback_tendsto {U : ℕ → WeakSobolevJet d 2 (volume.restrict T) T}
    {u : WeakSobolevJet d 2 (volume.restrict T) T} (ht : Tendsto U atTop (𝓝 u)) :
    Tendsto (fun n => graphShearH2Pullback hT r ψ hψ hC htrans hB (U n)) atTop
      (𝓝 (graphShearH2Pullback hT r ψ hψ hC htrans hB u)) :=
  ((graphShearH2Pullback hT r ψ hψ hC htrans hB).continuous.tendsto u).comp ht

theorem graphShearH2Pullback_test (φ : SpatialTest T) :
    graphShearH2Pullback hT r ψ hψ hC htrans hB (φ.allOrderJet 2)=
      (φ.pullbackSmoothHomeomorph (spatialGraphShear r ψ hψ.continuous htrans)
        (spatialGraphShear_contDiff r ψ hψ htrans) Subset.rfl).allOrderJet 2 := by
  have hS := hT.preimage (spatialGraphShear r ψ hψ.continuous htrans).continuous
  apply value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [graphShearH2Pullback_value,SpatialTest.allOrderJet_value,SpatialTest.allOrderJet_value,
    SpatialTest.pullbackSmoothHomeomorph_toLp _ _ _ _ (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)]

end WeakSobolevJet
end Carleman
