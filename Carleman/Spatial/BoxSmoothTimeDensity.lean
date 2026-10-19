module

public import Carleman.Spatial.DirichletSmoothTimeCore
public import Carleman.Spatial.BoxSmoothGraphDensity

/-! Smooth periodic zero-boundary functions are dense in the full weak box time graph. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ}

theorem box_smoothDirichletTimeCore_dense (hd : 0 < d) (a b : Fin d → ℝ)
    (hpos : ∀ i, a i < b i) (g : TimeGrid) :
    Dense (smoothDirichletTimeCore (openCoordinateBox_isOpen a b) hd
      (openCoordinateBox_isBounded a b) g : Set
        ((boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd
          (openCoordinateBox_isBounded a b)).model.PeriodicGraph g)) := by
  let B := (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b)).model
  let S := smoothDirichletTimeCore (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b) g
  apply B.dense_of_harmonic_approximation g S
  intro n x y
  obtain ⟨U,X,hUb,hUX,_,hX⟩ := exists_box_smooth_operator_graph_approximation hd a b hpos x
  obtain ⟨V,Y,hVb,hVY,_,hY⟩ := exists_box_smooth_operator_graph_approximation hd a b hpos y
  refine ⟨X,Y,hX,hY,?_⟩
  intro k
  exact harmonicGraph_mem_smoothDirichletTimeCore (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b) g n (X k) (Y k) (U k) (V k)
    (hUX k) (hVY k) (hUb k) (hVb k)

/-- One sequence controls the continuous trace, time derivative and actual Dirichlet operator. -/
theorem exists_box_smooth_periodic_graph_approximation (hd : 0 < d) (a b : Fin d → ℝ)
    (hpos : ∀ i, a i < b i) (g : TimeGrid) :
    let B := (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd
      (openCoordinateBox_isBounded a b)).model
    ∀ p : B.PeriodicGraph g,
      ∃ F : ℕ → (ℝ × SpatialCoordinates d) → ℝ, ∃ P : ℕ → B.PeriodicGraph g,
        (∀ n, ContDiff ℝ ∞ (F n)) ∧
        (∀ n, Function.Periodic (F n) (g.period,0)) ∧
        (∀ n t, ∀ x ∈ frontier (openCoordinateBox a b), F n (t,x)=0) ∧
        (∀ n, ∀ t : Icc 0 g.period,
          (P n).val.1 t =ᵐ[volume.restrict (openCoordinateBox a b)] (fun x => F n (t,x))) ∧
        Tendsto P atTop (𝓝 p) := by
  intro B p
  have hp := box_smoothDirichletTimeCore_dense hd a b hpos g p
  obtain ⟨P,hP,hPt⟩ := mem_closure_iff_seq_limit.mp hp
  choose F hF hFp hFb hFt using hP
  exact ⟨F,P,hF,hFp,hFb,hFt,hPt⟩

end Carleman
