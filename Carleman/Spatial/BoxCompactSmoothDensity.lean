module

public import Carleman.Spatial.BoxDirichletSmoothDensity
public import Carleman.Spatial.InteriorSmoothCutoff

/-! A fixed spatial cutoff makes the same zero-boundary H2 approximation compact. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d k : ℕ} {S : Set (SpatialCoordinates d)}

theorem coordinateDerivative_eqOn_of_eqOn (hS : IsOpen S)
    {f g : SpatialCoordinates d → ℝ} (he : EqOn f g S) (v : Fin k → Fin d) :
    EqOn (coordinateDerivative v f) (coordinateDerivative v g) S := by
  intro x hx
  have h : f =ᶠ[𝓝 x] g := Filter.eventually_of_mem (hS.mem_nhds hx) (fun y hy => he hy)
  exact congrArg (coordinateTensorEval v) ((h.iteratedFDeriv ℝ k).self_of_nhds)

theorem exists_box_dirichlet_compact_h2_approximation (a b : Fin d → ℝ)
    (hpos : ∀ i, a i < b i)
    (u : WeakSobolevJet d 2 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : WeakSobolevJet.truncate (by decide : 1 ≤ 2) u ∈ dirichletJetSpace (openCoordinateBox a b)) :
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ n, ∀ x ∈ frontier (openCoordinateBox a b), (U n).value x=0) ∧
      Tendsto (fun n => bochnerL2Norm (volume.restrict (openCoordinateBox a b))
        (fun x => (U n).value x-WeakSobolevJet.value u x)) atTop (𝓝 0) ∧
      (∀ v : Fin 1 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict (openCoordinateBox a b))
        (fun x => coordinateDerivative v (U n).value x-
          derivativeComponent (Sym.cons (v 0) Sym.nil) (WeakSobolevJet.field 1 u) x)) atTop (𝓝 0)) ∧
      (∀ v : Fin 2 → Fin d, Tendsto (fun n => bochnerL2Norm (volume.restrict (openCoordinateBox a b))
        (fun x => coordinateDerivative v (U n).value x-
          derivativeComponent (Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)) (WeakSobolevJet.field 2 u) x)) atTop (𝓝 0)) := by
  obtain ⟨F,hF,hb,h0,h1,h2⟩ := exists_box_dirichlet_smooth_h2_approximation a b hpos u hu
  obtain ⟨η,hη⟩ := exists_spatialTest_eq_one_on_compact isOpen_univ
    (openCoordinateBox_isBounded a b).isCompact_closure (subset_univ _)
  let U := fun n => η.mulSmooth (hF n)
  have he (n : ℕ) : EqOn (U n).value (F n) (openCoordinateBox a b) := by
    intro x hx
    change η.value x*F n x=F n x
    rw [hη x (subset_closure hx),one_mul]
  have herr {G H : ℕ → SpatialCoordinates d → ℝ}
      (h : ∀ n, EqOn (G n) (H n) (openCoordinateBox a b)) (z : SpatialCoordinates d → ℝ)
      (ht : Tendsto (fun n => bochnerL2Norm (volume.restrict (openCoordinateBox a b))
        (fun x => H n x-z x)) atTop (𝓝 0)) :
      Tendsto (fun n => bochnerL2Norm (volume.restrict (openCoordinateBox a b))
        (fun x => G n x-z x)) atTop (𝓝 0) := by
    apply ht.congr'
    apply Eventually.of_forall
    intro n
    apply bochnerL2Norm_congr_ae
    filter_upwards [ae_restrict_mem (openCoordinateBox_isOpen a b).measurableSet] with x hx
    rw [h n hx]
  refine ⟨U,?_,herr he _ h0,?_,?_⟩
  · intro n x hx
    change η.value x*F n x=0
    rw [hb n x hx,mul_zero]
  · intro v
    exact herr (fun n => coordinateDerivative_eqOn_of_eqOn (openCoordinateBox_isOpen a b) (he n) v) _ (h1 v)
  · intro v
    exact herr (fun n => coordinateDerivative_eqOn_of_eqOn (openCoordinateBox_isOpen a b) (he n) v) _ (h2 v)

end Carleman
