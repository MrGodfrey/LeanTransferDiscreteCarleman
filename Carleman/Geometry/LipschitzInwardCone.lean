module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-! Genuine inward balls in Lipschitz graph charts. Only Lipschitz regularity
of the graph is used; no high-order reflection or Sobolev extension is asserted. -/
@[expose] public noncomputable section
open Set Metric
open scoped NNReal
namespace Carleman
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A cone patch gives actual balls inside S at every sufficiently small scale,
with one fixed direction and height throughout an open region. -/
structure InwardConePatch (S : Set E) where
  region : Set E
  open_region : IsOpen region
  direction : E
  height : ℝ
  height_pos : 0 < height
  inward : ∀ x ∈ region, x ∈ S → ∀ t : ℝ, 0 < t → t ≤ height →
    closedBall (x+t • direction) t ⊆ S

omit [NormedSpace ℝ F] in
/-- In graph coordinates a vertical displacement dominates every horizontal
Lipschitz variation and every radius-t perturbation, including boundary bases. -/
theorem lipschitz_graph_inward_ball {K : ℝ≥0} {f : F → ℝ} (hf : LipschitzWith K f)
    {p : F × ℝ} (hp : f p.1 ≤ p.2) {t : ℝ} (ht : 0 < t) :
    closedBall (p.1,p.2+(K+2)*t) t ⊆ {z : F × ℝ | f z.1 < z.2} := by
  intro z hz
  rw [mem_closedBall,Prod.dist_eq,max_le_iff] at hz
  have hlip := hf.le_add_mul z.1 p.1
  have hk := mul_le_mul_of_nonneg_left hz.1 (K.coe_nonneg)
  have hv := (abs_le.mp (show |z.2-(p.2+(K+2)*t)| ≤ t by simpa only [Real.dist_eq] using hz.2)).1
  change f z.1 < z.2
  nlinarith

/-- A local Lipschitz graph through a bounded linear coordinate isomorphism
produces an inward cone on the smaller chart. No smoothness of f is required. -/
def InwardConePatch.ofGraph (S : Set E) (c : E) (R : ℝ) (hR : 0 < R)
    (e : E ≃L[ℝ] F × ℝ) {K : ℝ≥0} (f : F → ℝ) (hf : LipschitzWith K f)
    (hgraph : ∀ x ∈ ball c R, x ∈ S ↔ f (e (x-c)).1 < (e (x-c)).2) : InwardConePatch S := by
  let A := max 1 ‖e.toContinuousLinearMap‖
  let v := e.symm (0,(K+2)*A)
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨ball c (R/2),isOpen_ball,v,R/(2*(‖v‖+1)),by positivity,?_⟩
  intro x hx hxS t ht hheight z hz
  have hstep : t*(‖v‖+1) ≤ R/2 := by
    have he := (le_div_iff₀ (show 0 < 2*(‖v‖+1) by positivity)).mp hheight
    linarith
  have hdx : dist (x+t • v) x = t*‖v‖ := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
  have hzR : z ∈ ball c R := by
    have he := dist_triangle z (x+t • v) c
    have he' := dist_triangle (x+t • v) x c
    rw [hdx] at he'
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hz
    nlinarith
  have hxR : x ∈ ball c R := ball_subset_ball (by linarith) hx
  have hp : f (e (x-c)).1 ≤ (e (x-c)).2 := ((hgraph x hxR).mp hxS).le
  have hcenter : e ((x+t • v)-c) =
      ((e (x-c)).1,(e (x-c)).2+(K+2)*(A*t)) := by
    rw [show x+t • v-c=(x-c)+t • v by abel,map_add,map_smul]
    dsimp only [v]
    rw [e.apply_symm_apply]
    ext <;> simp
    ring
  have hball : e (z-c) ∈ closedBall
      ((e (x-c)).1,(e (x-c)).2+(K+2)*(A*t)) (A*t) := by
    rw [← hcenter,mem_closedBall,dist_eq_norm,← map_sub]
    rw [show (z-c)-((x+t • v)-c)=z-(x+t • v) by abel]
    calc
      _ ≤ ‖e.toContinuousLinearMap‖*‖z-(x+t • v)‖ := e.toContinuousLinearMap.le_opNorm _
      _ ≤ A*t := mul_le_mul (le_max_right _ _) (by simpa only [mem_closedBall,dist_eq_norm] using hz)
        (norm_nonneg _) hA.le
  exact (hgraph z hzR).mpr (lipschitz_graph_inward_ball hf hp (mul_pos hA ht) hball)

/-- Interior balls give patches with zero inward direction. -/
def InwardConePatch.ofInterior (S : Set E) (c : E) (R : ℝ) (hR : 0 < R)
    (hball : ball c R ⊆ S) : InwardConePatch S := by
  refine ⟨ball c (R/2),isOpen_ball,0,R/2,by positivity,?_⟩
  intro x hx _ t _ ht z hz
  apply hball
  simp only [smul_zero,add_zero,mem_closedBall] at hz
  rw [mem_ball] at hx ⊢
  have := dist_triangle z x c
  linarith

/-- Explicit Lipschitz graph charts. The graph has only Lipschitz regularity;
this condition does not postulate any Sobolev extension or interpolation. -/
def HasLipschitzGraphCharts (S : Set E) (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Prop :=
  ∀ c ∈ frontier S, ∃ R : ℝ, 0 < R ∧ ∃ e : E ≃L[ℝ] F × ℝ,
    ∃ K : ℝ≥0, ∃ f : F → ℝ, LipschitzWith K f ∧
      ∀ x ∈ ball c R, x ∈ S ↔ f (e (x-c)).1 < (e (x-c)).2

/-- Every closure point has a real cone patch, using its interior ball or its
boundary graph. Boundary regularity is used only in the second case. -/
theorem exists_inwardConePatch_of_mem_closure {S : Set E} (hS : IsOpen S)
    (hgraph : HasLipschitzGraphCharts S F) {x : E} (hx : x ∈ closure S) :
    ∃ p : InwardConePatch S, x ∈ p.region := by
  classical
  by_cases hxS : x ∈ S
  · obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hS x hxS
    refine ⟨InwardConePatch.ofInterior S x R hR hball,?_⟩
    change x ∈ ball x (R/2)
    exact mem_ball_self (by positivity)
  · have hfront : x ∈ frontier S := by
      rw [frontier,hS.interior_eq]
      exact ⟨hx,hxS⟩
    obtain ⟨R,hR,e,K,f,hf,hlocal⟩ := hgraph x hfront
    refine ⟨InwardConePatch.ofGraph S x R hR e f hf hlocal,?_⟩
    change x ∈ ball x (R/2)
    exact mem_ball_self (by positivity)

/-- A bounded open Lipschitz domain has finitely many genuine inward-ball
patches and one positive height, chosen before the point or scale. This is a
geometric theorem only; the weak Taylor/averaging estimate is a separate step. -/
theorem finite_uniform_inwardCone_cover [ProperSpace E] {S : Set E}
    (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
    (hgraph : HasLipschitzGraphCharts S F) :
    ∃ P : Finset (InwardConePatch S), ∃ δ : ℝ, 0 < δ ∧
      closure S ⊆ ⋃ p ∈ P, p.region ∧
      ∀ p ∈ P, ∀ x ∈ p.region, x ∈ S → ∀ t : ℝ, 0 < t → t ≤ δ →
        closedBall (x+t • p.direction) t ⊆ S := by
  classical
  have hcover : closure S ⊆ ⋃ p : InwardConePatch S, p.region := by
    intro x hx
    obtain ⟨p,hp⟩ := exists_inwardConePatch_of_mem_closure hS hgraph hx
    exact mem_iUnion.mpr ⟨p,hp⟩
  obtain ⟨P,hP⟩ := hbounded.isCompact_closure.elim_finite_subcover
    (fun p : InwardConePatch S => p.region) (fun p => p.open_region) hcover
  have hheight : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ P, δ ≤ p.height := by
    clear hP
    induction P using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert p P _ ih =>
      obtain ⟨δ,hδ,hd⟩ := ih
      refine ⟨min p.height δ,lt_min p.height_pos hδ,?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hd q hq)
  obtain ⟨δ,hδ,hd⟩ := hheight
  exact ⟨P,δ,hδ,hP,fun p hp x hx hxS t ht htd => p.inward x hx hxS t ht (htd.trans (hd p hp))⟩
end Carleman
