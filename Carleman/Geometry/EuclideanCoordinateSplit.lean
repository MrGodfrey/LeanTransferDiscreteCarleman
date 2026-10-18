module

public import Carleman.Spatial.SobolevJet
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Split any Euclidean coordinate into the interval factor. Both the
actual continuous linear equivalence and its exact volume preservation
are proved, including the zero-dimensional transverse factor. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def coordinateSplitMeasurable (i : Fin (d+1)) :
    SpatialCoordinates (d+1) ≃ᵐ SpatialCoordinates d × ℝ :=
  ((MeasurableEquiv.toLp 2 (Fin (d+1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i)).trans
    ((MeasurableEquiv.prodComm : ℝ × (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) × ℝ).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin d → ℝ)) (MeasurableEquiv.refl ℝ)))

theorem coordinateSplitMeasurable_apply (i : Fin (d+1)) (x : SpatialCoordinates (d+1)) :
    coordinateSplitMeasurable i x=(WithLp.toLp 2 (fun j => x (i.succAbove j)),x i) := rfl

theorem coordinateSplitMeasurable_symm_apply (i : Fin (d+1)) (x : SpatialCoordinates d × ℝ) :
    (coordinateSplitMeasurable i).symm x=WithLp.toLp 2 (i.insertNth x.2 (fun j => x.1 j)) := rfl

def coordinateSplit (i : Fin (d+1)) : SpatialCoordinates (d+1) ≃L[ℝ] SpatialCoordinates d × ℝ :=
  (show SpatialCoordinates (d+1) ≃ₗ[ℝ] SpatialCoordinates d × ℝ from
    { toEquiv := (coordinateSplitMeasurable i).toEquiv
      map_add' := fun x y => by
        apply Prod.ext
        · apply PiLp.ext
          intro j
          rfl
        · rfl
      map_smul' := fun c x => by
        apply Prod.ext
        · apply PiLp.ext
          intro j
          rfl
        · rfl }).toContinuousLinearEquiv

theorem coordinateSplit_apply (i : Fin (d+1)) (x : SpatialCoordinates (d+1)) :
    coordinateSplit i x=(WithLp.toLp 2 (fun j => x (i.succAbove j)),x i) := rfl

theorem coordinateSplit_measurePreserving (i : Fin (d+1)) :
    MeasurePreserving (coordinateSplit i) volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (Fin (d+1))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) i
  have h3 := Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin d → ℝ)))
  have h4 := (PiLp.volume_preserving_toLp (Fin d)).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  exact h4.comp (h3.comp (h2.comp h1))

theorem coordinateSplit_basis (i : Fin (d+1)) :
    coordinateSplit i (EuclideanSpace.basisFun (Fin (d+1)) ℝ i)=(0,1) := by
  rw [coordinateSplit_apply]
  apply Prod.ext
  · apply PiLp.ext
    intro j
    simp [EuclideanSpace.basisFun_apply,Fin.succAbove_ne]
  · simp [EuclideanSpace.basisFun_apply]

end Carleman
