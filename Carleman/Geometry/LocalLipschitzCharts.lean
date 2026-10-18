module

public import Carleman.Geometry.LipschitzInwardCone

/-! The local boundary-chart hypothesis uses a graph function Lipschitz only
on a horizontal ball. The global graph used by the cone construction is obtained
by the proved real-valued Lipschitz extension theorem, not postulated. -/
@[expose] public noncomputable section
open Set Metric
open scoped NNReal Topology
namespace Carleman
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A usual local cylindrical boundary chart. The product norm encodes the
horizontal ball and vertical interval; f is constrained only on that ball.
The continuous linear coordinates include the usual orthogonal coordinates. -/
structure LocalLipschitzGraphChart (S : Set E) (c : E) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  coordinates : E ≃L[ℝ] F × ℝ
  radius : ℝ
  radius_pos : 0 < radius
  constant : ℝ≥0
  graph : F → ℝ
  lipschitz : LipschitzOnWith constant graph (ball 0 radius)
  graph_zero : graph 0 = 0
  local_graph : ∀ x, ‖coordinates (x-c)‖ < radius →
    (x ∈ S ↔ graph (coordinates (x-c)).1 < (coordinates (x-c)).2)

/-- The bounded Lipschitz domain convention used here: an open bounded set
with local Lipschitz cylinder charts at every boundary point. Connectedness is
not needed for the analytic estimates. No global graph or Sobolev extension
is part of this hypothesis. -/
structure IsBoundedLipschitzDomain (S : Set E) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop where
  isOpen : IsOpen S
  isBounded : Bornology.IsBounded S
  local_charts : ∀ c ∈ frontier S, Nonempty (LocalLipschitzGraphChart S c F)

/-- McShane's real-valued Lipschitz extension agrees with the original local
graph, and a smaller physical ball stays in the original cylinder. -/
theorem LocalLipschitzGraphChart.exists_global_graph {S : Set E} {c : E}
    (chart : LocalLipschitzGraphChart S c F) :
    ∃ R : ℝ, 0 < R ∧ ∃ f : F → ℝ, LipschitzWith chart.constant f ∧
      ∀ x ∈ ball c R,
        x ∈ S ↔ f (chart.coordinates (x-c)).1 < (chart.coordinates (x-c)).2 := by
  obtain ⟨f,hf,heq⟩ := chart.lipschitz.extend_real
  let A := max 1 ‖chart.coordinates.toContinuousLinearMap‖
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨chart.radius/A,div_pos chart.radius_pos hA,f,hf,?_⟩
  intro x hx
  have hxnorm : ‖x-c‖ < chart.radius/A := by simpa only [mem_ball,dist_eq_norm] using hx
  have hcoord : ‖chart.coordinates (x-c)‖ < chart.radius := by
    calc
      _ ≤ ‖chart.coordinates.toContinuousLinearMap‖*‖x-c‖ :=
        chart.coordinates.toContinuousLinearMap.le_opNorm _
      _ ≤ A*‖x-c‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ < chart.radius := by nlinarith [(lt_div_iff₀ hA).mp hxnorm]
  have hhor : (chart.coordinates (x-c)).1 ∈ ball 0 chart.radius := by
    rw [mem_ball,dist_zero_right]
    exact (norm_fst_le _).trans_lt hcoord
  rw [← heq hhor]
  exact chart.local_graph x hcoord

/-- The previous global-graph interface follows from the local boundary
definition. It is not an additional assumption on the domain. -/
theorem IsBoundedLipschitzDomain.global_graph_charts {S : Set E}
    (hS : IsBoundedLipschitzDomain S F) : HasLipschitzGraphCharts S F := by
  intro c hc
  obtain ⟨chart⟩ := hS.local_charts c hc
  obtain ⟨R,hR,f,hf,hlocal⟩ := chart.exists_global_graph
  exact ⟨R,hR,chart.coordinates,chart.constant,f,hf,hlocal⟩

/-- Conversely, the usable global-graph interface supplies the usual local
cylinder charts. The graph passes through the boundary center as a consequence
of the local domain identity and continuity, not as an extra assumption. -/
theorem HasLipschitzGraphCharts.local_charts {S : Set E} (hS : IsOpen S)
    (hgraph : HasLipschitzGraphCharts S F) :
    ∀ c ∈ frontier S, Nonempty (LocalLipschitzGraphChart S c F) := by
  intro c hc
  obtain ⟨R,hR,e,K,f,hf,hloc⟩ := hgraph c hc
  have hcnot : c ∉ S := by
    have he := hc.2
    simpa only [hS.interior_eq] using he
  have hnonneg : 0 ≤ f 0 := by
    have he := mt ((hloc c (mem_ball_self hR)).mpr) hcnot
    simpa only [sub_self,map_zero,Prod.fst_zero,Prod.snd_zero,not_lt] using he
  let g := fun x => f (e (x-c)).1-(e (x-c)).2
  have hg : Continuous g :=
    (hf.continuous.comp ((e.continuous.comp (continuous_id.sub continuous_const)).fst)).sub
      ((e.continuous.comp (continuous_id.sub continuous_const)).snd)
  have hnonpos : f 0 ≤ 0 := by
    by_contra hn
    have hp : 0 < g c := by simpa only [g,sub_self,map_zero,Prod.fst_zero,Prod.snd_zero,sub_zero] using lt_of_not_ge hn
    have hpos := (isOpen_lt continuous_const hg).mem_nhds hp
    have hfreq := ((mem_closure_iff_frequently.mp hc.1).and_eventually (ball_mem_nhds c hR)).and_eventually hpos
    obtain ⟨x,⟨hxS,hxR⟩,hxg⟩ := hfreq.exists
    have hxneg : g x < 0 := sub_neg.mpr ((hloc x hxR).mp hxS)
    exact (not_lt_of_ge hxg.le) hxneg
  let A := max 1 ‖e.symm.toContinuousLinearMap‖
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨⟨e,R/A,div_pos hR hA,K,f,hf.lipschitzOnWith,le_antisymm hnonpos hnonneg,?_⟩⟩
  intro x hx
  apply hloc
  rw [mem_ball,dist_eq_norm]
  have hbound : ‖x-c‖ ≤ A*‖e (x-c)‖ := by
    calc
      _ = ‖e.symm (e (x-c))‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖*‖e (x-c)‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  nlinarith [(lt_div_iff₀ hA).mp hx]

theorem boundedLipschitz_iff_global_graph_charts {S : Set E} :
    IsBoundedLipschitzDomain S F ↔
      IsOpen S ∧ Bornology.IsBounded S ∧ HasLipschitzGraphCharts S F := by
  constructor
  · intro h
    exact ⟨h.isOpen,h.isBounded,h.global_graph_charts⟩
  · rintro ⟨ho,hb,hg⟩
    exact ⟨ho,hb,hg.local_charts ho⟩

/-- Real finite cone geometry from local Lipschitz boundary data. -/
theorem IsBoundedLipschitzDomain.finite_uniform_cones [ProperSpace E] {S : Set E}
    (hS : IsBoundedLipschitzDomain S F) :
    ∃ P : Finset (InwardConePatch S), ∃ δ : ℝ, 0 < δ ∧
      closure S ⊆ ⋃ p ∈ P, p.region ∧
      ∀ p ∈ P, ∀ x ∈ p.region, x ∈ S → ∀ t : ℝ, 0 < t → t ≤ δ →
        closedBall (x+t • p.direction) t ⊆ S :=
  finite_uniform_inwardCone_cover hS.isOpen hS.isBounded hS.global_graph_charts
end Carleman
