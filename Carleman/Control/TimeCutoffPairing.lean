module

public import Carleman.Control.ObservedRegionLp
public import Carleman.Spatial.MultiplierContinuity

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace Carleman
variable {α β V H : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {μ : Measure α} {ν : Measure β}

theorem BoundedMultiplier.compLpL_map (w : BoundedMultiplier μ) (E : V →L[ℝ] H)
    (u : Lp V 2 μ) : E.compLpL 2 μ (w.map u)=w.map (E.compLpL 2 μ u) := by
  apply Lp.ext
  filter_upwards [E.coeFn_compLpL (w.map u),w.map_ae u,
    w.map_ae (E.compLpL 2 μ u),E.coeFn_compLpL u] with t h1 h2 h3 h4
  rw [h1,h2,h3,h4,_root_.map_smul]

theorem cutoff_map_idempotent (s : Set α) (hs : MeasurableSet s) (u : Lp V 2 μ) :
    (BoundedMultiplier.cutoff s hs).map ((BoundedMultiplier.cutoff s hs).map u)=
      (BoundedMultiplier.cutoff s hs).map u := by
  classical
  apply Lp.ext
  filter_upwards [(BoundedMultiplier.cutoff s hs).map_ae u,
    (BoundedMultiplier.cutoff s hs).map_ae ((BoundedMultiplier.cutoff s hs).map u)] with t h1 h2
  rw [h2,h1]
  by_cases ht : t∈s <;> simp [BoundedMultiplier.cutoff,ht]

theorem cutoff_inner_integral (s : Set α) (hs : MeasurableSet s) (u v : Lp V 2 μ) :
    inner ℝ u ((BoundedMultiplier.cutoff s hs).map v)=∫ t in s, inner ℝ (u t) (v t) ∂μ := by
  classical
  rw [L2.inner_def,← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [(BoundedMultiplier.cutoff s hs).map_ae v] with t ht
  rw [ht]
  by_cases hx : t∈s <;> simp [BoundedMultiplier.cutoff,hx]

theorem cutoff_inner_cutoff (s : Set α) (hs : MeasurableSet s) (u v : Lp V 2 μ) :
    inner ℝ u ((BoundedMultiplier.cutoff s hs).map v)=
      inner ℝ ((BoundedMultiplier.cutoff s hs).map u) ((BoundedMultiplier.cutoff s hs).map v) := by
  classical
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(BoundedMultiplier.cutoff s hs).map_ae u,
    (BoundedMultiplier.cutoff s hs).map_ae v] with t hu hv
  rw [hu,hv]
  by_cases ht : t∈s <;> simp [BoundedMultiplier.cutoff,ht]

theorem cutoff_multiplier_pairing (s : Set α) (hs : MeasurableSet s)
    (b : BoundedMultiplier μ) (u : Lp ℝ 2 μ) :
    inner ℝ (b.map u) ((BoundedMultiplier.cutoff s hs).map u)=
      inner ℝ (b.map ((BoundedMultiplier.cutoff s hs).map u)) ((BoundedMultiplier.cutoff s hs).map u) := by
  rw [cutoff_inner_cutoff]
  congr 1
  apply Lp.ext
  let W := BoundedMultiplier.cutoff (ν := μ) s hs
  filter_upwards [W.map_ae (b.map u),b.map_ae u,b.map_ae (W.map u),W.map_ae u]
    with t h1 h2 h3 h4
  rw [h1,h2,h3,h4,smul_comm]


end Carleman
