module

public import Carleman.Spatial.ClassicalHarmonicTimeCore
public import Carleman.Spatial.BoxSmoothGraphDensity

/-! Full weak graph approximation with the actual classical time derivative and negative Laplacian. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ}

theorem box_classicalDirichletTimeCore_dense (hd : 0 < d) (a b : Fin d → ℝ)
    (hpos : ∀ i, a i < b i) (g : TimeGrid) :
    Dense (classicalDirichletTimeCore (openCoordinateBox_isOpen a b) hd
      (openCoordinateBox_isBounded a b) g : Set
        ((boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd
          (openCoordinateBox_isBounded a b)).model.PeriodicGraph g)) := by
  let B := (boundedDirichletOriginalForm (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b)).model
  let S := classicalDirichletTimeCore (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b) g
  apply B.dense_of_harmonic_approximation g S
  intro n x y
  obtain ⟨U,X,hUb,hUX,hUA,hX⟩ := exists_box_smooth_operator_graph_approximation hd a b hpos x
  obtain ⟨V,Y,hVb,hVY,hVA,hY⟩ := exists_box_smooth_operator_graph_approximation hd a b hpos y
  refine ⟨X,Y,hX,hY,?_⟩
  intro k
  exact harmonicGraph_mem_classicalDirichletTimeCore (openCoordinateBox_isOpen a b) hd
    (openCoordinateBox_isBounded a b) g n (X k) (Y k) (U k) (V k)
    (hUX k) (hVY k) (hUA k) (hVA k) (hUb k) (hVb k)

/-- One sequence controls the continuous trace, time derivative and actual Dirichlet operator. -/
theorem exists_box_classical_periodic_graph_approximation (hd : 0 < d) (a b : Fin d → ℝ)
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
        (∀ n, ∀ᵐ t ∂g.timeMeasure,
          ((P n).val.2.1 t =ᵐ[volume.restrict (openCoordinateBox a b)]
            (fun x => deriv (fun s => F n (s,x)) t)) ∧
          ((P n).val.2.2 t =ᵐ[volume.restrict (openCoordinateBox a b)]
            (fun x => -spatialLaplacian (fun y => F n (t,y)) x))) ∧
        Tendsto P atTop (𝓝 p) := by
  intro B p
  have hp := box_classicalDirichletTimeCore_dense hd a b hpos g p
  obtain ⟨P,hP,hPt⟩ := mem_closure_iff_seq_limit.mp hp
  choose F hF hFp hFb hFt hFd using hP
  refine ⟨F,P,hF,hFp,hFb,hFt,?_,hPt⟩
  intro n
  filter_upwards [hFd n] with t ht
  constructor
  · filter_upwards [ht.1] with x hx
    simpa only [spaceTime_timeD (hF n)] using hx
  · filter_upwards [ht.2] with x hx
    simpa only [spaceTime_directionalLap (hF n)] using hx

end Carleman
