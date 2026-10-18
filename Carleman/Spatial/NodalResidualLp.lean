module

public import Carleman.Spatial.SimplicialProductResidual
public import Carleman.Spatial.MultiplierAlgebra

/-! The residual's pointwise representative is exactly the actual L²
multiplier difference and the genuine nodal test class. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem nodalProductResidual_lp (hS : MeasurableSet S) (hM : M.FaceMatching)
    (w : BoundedMultiplier (volume.restrict S)) (f : SpatialCoordinates d → ℝ)
    (u e : Lp ℝ 2 (volume.restrict S)) (hu : u=M.nodalLp hS hM f)
    (he : e =ᵐ[volume.restrict S] M.nodalProductResidual w.value f) :
    e=w.map u-M.nodalLp hS hM (fun x => w.value x*f x) := by
  apply Lp.ext
  rw [hu]
  filter_upwards [he,w.map_ae (M.nodalLp hS hM f),M.nodalLp_ae hS hM f,
    M.nodalLp_ae hS hM (fun x => w.value x*f x),
    Lp.coeFn_sub (w.map (M.nodalLp hS hM f)) (M.nodalLp hS hM (fun x => w.value x*f x))]
    with x hx hw hf hI hsub
  rw [hx,hsub]
  simp only [Pi.sub_apply,hw,hf,hI,smul_eq_mul,nodalProductResidual]

end Carleman.SimplicialPartition
