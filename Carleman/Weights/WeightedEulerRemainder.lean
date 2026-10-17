module

public import Carleman.Weights.EulerTemporalPerturbation
public import Carleman.Weights.SpacetimeCommutator

/-! Weighted Euler graph estimate with its actual spatial commutator remainder.
The time commutator is absorbed for all domain states and both orientations. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω} (ρ : SpatialProfile ν)

def weightedNodes (g : TimeGrid) (w : TimeWeight) (τ : ℝ) (D : Submodule ℝ (Lp E 2 ν))
    (hw : ∀ i, ∀ u : D, (ρ.multiplier w τ (g.nodeTime i)).map (u : Lp E 2 ν) ∈ D)
    (u : g.Sequence D) : g.Sequence D :=
  fun i => ⟨(ρ.multiplier w τ (g.nodeTime i)).map (u i : Lp E 2 ν), hw i (u i)⟩

theorem weightedNodes_value (g : TimeGrid) (w : TimeWeight) (τ : ℝ) (D : Submodule ℝ (Lp E 2 ν))
    (hw : ∀ i, ∀ u : D, (ρ.multiplier w τ (g.nodeTime i)).map (u : Lp E 2 ν) ∈ D)
    (u : g.Sequence D) :
    (fun i => (ρ.weightedNodes g w τ D hw u i : Lp E 2 ν)) =
      ρ.nodeMap g w τ (fun i => (u i : Lp E 2 ν)) := rfl

theorem nodeMap_l2Norm (g : TimeGrid) (w : TimeWeight) (τ : ℝ)
    (u : g.Sequence (Lp E 2 ν)) :
    g.l2Norm (ρ.nodeMap g w τ u) =
      g.weightedNorm (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) u := rfl
end Carleman.SpatialProfile

namespace Carleman.CoerciveForm
variable {Ω E V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : CoerciveForm (Lp E 2 ν) V) (ρ : SpatialProfile ν)

theorem weighted_euler_identity (g : TimeGrid) (s : Orientation) (w : TimeWeight) (τ : ℝ)
    (hw : ∀ i, ∀ u : b.domain, (ρ.multiplier w τ (g.nodeTime i)).map (u : Lp E 2 ν) ∈ b.domain)
    (μ : g.Sequence ℝ) (u : g.Sequence b.domain) :
    let v := ρ.weightedNodes g w τ b.domain hw u
    let M := ρ.nodeMap g w τ
    b.eulerResidual g s μ v = M (b.eulerResidual g s μ u) +
      ((fun i => b.operator (v i)) - M (fun i => b.operator (u i))) +
      ρ.eulerTimeCommutator g s w τ (fun i => (u i : Lp E 2 ν)) := by
  intro v M
  funext i
  simp only [eulerResidual,Pi.add_apply,Pi.sub_apply,SpatialProfile.eulerTimeCommutator,
    SpatialProfile.nodeMap,LinearMap.coe_mk,AddHom.coe_mk]
  have hv : (fun j => (v j : Lp E 2 ν)) =
      (fun j => (ρ.multiplier w τ (g.nodeTime j)).map (u j : Lp E 2 ν)) := rfl
  rw [hv]
  change _ = _
  dsimp only [M,SpatialProfile.nodeMap,LinearMap.coe_mk,AddHom.coe_mk]
  simp only [eulerResidual,BoundedMultiplier.map_add,BoundedMultiplier.map_smul]
  have hvi : (v i : Lp E 2 ν) = (ρ.multiplier w τ (g.nodeTime i)).map (u i : Lp E 2 ν) := rfl
  rw [hvi]
  abel

/-- Spatial commutator is retained explicitly; no weighted graph or parameter
interpolation estimate is assumed. The constant 6 and thresholds are T-uniform. -/
theorem weighted_euler_graph_remainder_uniform (m : ℕ) (hm : 0 < m)
    (β τStar : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ (hw : ∀ i, ∀ u : b.domain,
          (ρ.multiplier w τ (g.nodeTime i)).map (u : Lp E 2 ν) ∈ b.domain)
          (u : g.Sequence b.domain),
        let M := ρ.nodeMap g w τ
        let v := ρ.weightedNodes g w τ b.domain hw u
        let μ := fun i => (L*w.nodes g i)^(2*m)
        g.l2Norm (M (s.difference g (fun i => (u i : Lp E 2 ν)))) +
          g.l2Norm (M (fun i => b.operator (u i))) +
          g.l2Norm (fun i => μ i • M (fun j => (u j : Lp E 2 ν)) i) ≤
            6*(g.l2Norm (M (b.eulerResidual g s μ u)) +
              g.l2Norm ((fun i => b.operator (v i)) - M (fun i => b.operator (u i)))) := by
  obtain ⟨L₁,δ₁,hL₁,hδ₁,hsmall⟩ := ρ.eulerTimeCommutator_small_uniform
    (E := E) m hm β τStar (1/12) hβ hτStar (by norm_num)
  refine ⟨max L₁ (eulerShiftThreshold m β), min δ₁ (cellThreshold β 0 0),
    hL₁.trans (le_max_left _ _),lt_min hδ₁ (cellThreshold_pos hβ le_rfl le_rfl),?_⟩
  intro g s w h L τ hL hmesh hτ hw u M v μ
  let U := fun i => (u i : Lp E 2 ν)
  let Z := fun i => (v i : Lp E 2 ν)
  let R := (fun i => b.operator (v i)) - M (fun i => b.operator (u i))
  let F := M (b.eulerResidual g s μ u)
  let B := ρ.eulerTimeCommutator g s w τ U
  have hv : Z = M U := rfl
  have hB : g.l2Norm B ≤ (1/12)*g.l2Norm (fun i => μ i • Z i) := by
    exact hsmall g s w h L τ ((le_max_left _ _).trans hL)
      (hmesh.trans (min_le_left _ _)) hτ U
  have he : b.eulerResidual g s μ v = F+R+B :=
    b.weighted_euler_identity ρ g s w τ hw μ u
  have heN : g.l2Norm (b.eulerResidual g s μ v) ≤ g.l2Norm F+g.l2Norm R+g.l2Norm B := by
    rw [he]
    linarith [g.l2Norm_add_le (F+R) B,g.l2Norm_add_le F R]
  have hG := b.euler_unweighted_graph hm ((le_max_right _ _).trans hL)
    g w h (hmesh.trans (min_le_right _ _)) s v
  change g.l2Norm (s.difference g Z)+g.l2Norm (fun i => b.operator (v i))+
    g.l2Norm (fun i => μ i • Z i) ≤ 3*g.l2Norm (b.eulerResidual g s μ v) at hG
  have hD : g.l2Norm (M (s.difference g U)) ≤ g.l2Norm (s.difference g Z)+g.l2Norm B := by
    have hid : M (s.difference g U) = s.difference g Z - B := by
      dsimp [B,SpatialProfile.eulerTimeCommutator]
      rw [hv]
      abel
    rw [hid]
    exact g.l2Norm_sub_le _ _
  have hA : g.l2Norm (M (fun i => b.operator (u i))) ≤
      g.l2Norm (fun i => b.operator (v i))+g.l2Norm R := by
    have hid : M (fun i => b.operator (u i)) = (fun i => b.operator (v i))-R := by dsimp [R]; abel
    rw [hid]
    exact g.l2Norm_sub_le _ _
  change g.l2Norm (M (s.difference g U))+g.l2Norm (M (fun i => b.operator (u i)))+
    g.l2Norm (fun i => μ i • Z i) ≤ 6*(g.l2Norm F+g.l2Norm R)
  linarith [g.l2Norm_nonneg F,g.l2Norm_nonneg R,g.l2Norm_nonneg (M (s.difference g U)),
    g.l2Norm_nonneg (M (fun i => b.operator (u i)))]
end Carleman.CoerciveForm
