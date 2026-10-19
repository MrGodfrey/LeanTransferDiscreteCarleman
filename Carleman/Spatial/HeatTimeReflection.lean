module

public import Carleman.Spatial.BoxObservationIntegral
public import Carleman.Spatial.SpacetimeHeatIdentity

/-! Actual time reflection, its measure preservation, and its first two time derivatives. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

def heatTimeReflection (T : ℝ) (tx : ℝ × SpatialCoordinates d) : ℝ × SpatialCoordinates d :=
  (T-tx.1,tx.2)

theorem heatTimeReflection_contDiff (T : ℝ) : ContDiff ℝ ∞ (heatTimeReflection (d := d) T) :=
  (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

theorem heatTimeReflection_involutive (T : ℝ) : Function.Involutive (heatTimeReflection (d := d) T) := by
  intro tx
  simp [heatTimeReflection]

theorem time_reflection_mem_interval {T t : ℝ} (ht : t ∈ Icc 0 T) : T-t ∈ Icc 0 T := by
  constructor <;> linarith [ht.1,ht.2]

theorem heatTimeReflection_periodic {u : (ℝ × SpatialCoordinates d) → ℝ} {T : ℝ}
    (hu : Function.Periodic u (T,0)) : Function.Periodic (fun tx => u (heatTimeReflection T tx)) (T,0) := by
  intro tx
  have he : heatTimeReflection T (tx+(T,0))=heatTimeReflection T tx-(T,0) := by
    ext <;> simp [heatTimeReflection]
  change u (heatTimeReflection T (tx+(T,0)))=u (heatTimeReflection T tx)
  rw [he,hu.sub_eq]

theorem time_reflection_measurePreserving (T : ℝ) :
    MeasurePreserving (fun t : ℝ => T-t) (volume.restrict (Icc 0 T)) (volume.restrict (Icc 0 T)) := by
  have he : (fun t : ℝ => T-t) ⁻¹' Icc 0 T=Icc 0 T := by
    ext t
    simp only [mem_preimage,mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  simpa only [he] using (volume.measurePreserving_sub_left T).restrict_preimage
    (measurableSet_Icc : MeasurableSet (Icc (0:ℝ) T))

theorem heatTimeReflection_measurePreserving (a b : Fin d → ℝ) (T : ℝ) :
    MeasurePreserving (heatTimeReflection T)
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b)))
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b))) :=
  (time_reflection_measurePreserving T).prod (MeasurePreserving.id _)

theorem boxTimeIntegral_reflection (a b : Fin d → ℝ) (T : ℝ)
    (f : (ℝ × SpatialCoordinates d) → ℝ) :
    boxTimeIntegral a b T (fun tx => f (heatTimeReflection T tx))=boxTimeIntegral a b T f := by
  let e := MeasurableEquiv.ofInvolutive (heatTimeReflection (d := d) T)
    (heatTimeReflection_involutive T) (heatTimeReflection_contDiff T).continuous.measurable
  exact (heatTimeReflection_measurePreserving a b T).integral_comp e.measurableEmbedding f

theorem deriv_time_reflection {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (T t : ℝ) :
    deriv (fun s => q (T-s)) t = -deriv q (T-t) := by
  have hh := ((hq.differentiable (by simp) (T-t)).hasDerivAt).comp t
    ((hasDerivAt_id t).const_sub T)
  convert! hh.deriv using 1
  ring

theorem deriv_deriv_time_reflection {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (T t : ℝ) :
    deriv (deriv (fun s => q (T-s))) t = deriv (deriv q) (T-t) := by
  have he : deriv (fun s => q (T-s))=(fun s => -deriv q (T-s)) :=
    funext (deriv_time_reflection hq T)
  have hq' : ContDiff ℝ ∞ (deriv q) := smoothD_contDiff hq 1
  have hh := (((hq'.differentiable (by simp) (T-t)).hasDerivAt).comp t
    ((hasDerivAt_id t).const_sub T)).neg
  rw [he]
  convert! hh.deriv using 1
  ring

theorem spaceTimeHeat_time_reflection {u : (ℝ × SpatialCoordinates d) → ℝ}
    (hu : ContDiff ℝ ∞ u) (T t : ℝ) (x : SpatialCoordinates d) :
    spaceTimeHeat (fun tx => u (heatTimeReflection T tx)) (t,x)=
      -deriv (fun s => u (s,x)) (T-t)-spatialLaplacian (fun y => u (T-t,y)) x := by
  have hs : ContDiff ℝ ∞ (fun s => u (s,x)) := hu.comp (contDiff_id.prodMk contDiff_const)
  change deriv (fun s => u (T-s,x)) t-spatialLaplacian (fun y => u (T-t,y)) x=_
  rw [deriv_time_reflection hs]

end Carleman
