module

public import Carleman.Spatial.SimplicialGlobalSobolev
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.MetricSpace.Thickening

/-! Inward homotheties put the closed support of a zero extension strictly
inside an open convex domain, with a positive buffer for convolution. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def centeredDilation (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0) :
    SpatialCoordinates d ≃ₜ SpatialCoordinates d where
  toFun x := a + r • (x-a)
  invFun x := a + r⁻¹ • (x-a)
  left_inv x := by simp [smul_smul,hr]
  right_inv x := by simp [smul_smul,hr]
  continuous_toFun := continuous_const.add ((continuous_id.sub continuous_const).const_smul r)
  continuous_invFun := continuous_const.add ((continuous_id.sub continuous_const).const_smul r⁻¹)

theorem centeredDilation_mem {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hconv : Convex ℝ S)
    {a : SpatialCoordinates d} (ha : a ∈ S) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {x : SpatialCoordinates d} (hx : x ∈ closure S) : centeredDilation a r hr.ne' x ∈ S := by
  have hh := hconv.combo_interior_closure_mem_interior (hS.interior_eq.symm ▸ ha) hx
    (sub_pos.mpr hr1) hr.le (sub_add_cancel 1 r)
  rw [hS.interior_eq] at hh
  convert hh using 1
  change a + r • (x-a) = (1-r) • a + r • x
  module

def contractedFunction (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0)
    (f : SpatialCoordinates d → ℝ) : SpatialCoordinates d → ℝ :=
  f ∘ (centeredDilation a r hr).symm

theorem contractedFunction_tsupport (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0)
    (f : SpatialCoordinates d → ℝ) :
    tsupport (contractedFunction a r hr f) = centeredDilation a r hr '' tsupport f := by
  rw [contractedFunction,tsupport_comp_eq_preimage]
  ext x
  constructor
  · intro hx
    exact ⟨(centeredDilation a r hr).symm x,hx,(centeredDilation a r hr).apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa only [Set.mem_preimage,Homeomorph.symm_apply_apply] using hy

theorem contractedFunction_compact (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0)
    {f : SpatialCoordinates d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (contractedFunction a r hr f) :=
  hf.comp_homeomorph (centeredDilation a r hr).symm

theorem contractedFunction_support_inside {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (hconv : Convex ℝ S) {a : SpatialCoordinates d} (ha : a ∈ S)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {f : SpatialCoordinates d → ℝ}
    (hf : tsupport f ⊆ closure S) : tsupport (contractedFunction a r hr.ne' f) ⊆ S := by
  rw [contractedFunction_tsupport]
  rintro _ ⟨x,hx,rfl⟩
  exact centeredDilation_mem hS hconv ha hr hr1 (hf hx)

theorem contractedFunction_buffer {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (hconv : Convex ℝ S) {a : SpatialCoordinates d} (ha : a ∈ S)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {f : SpatialCoordinates d → ℝ}
    (hf : HasCompactSupport f) (hsupp : tsupport f ⊆ closure S) :
    ∃ δ > (0 : ℝ), Metric.cthickening δ (tsupport (contractedFunction a r hr.ne' f)) ⊆ S :=
  (contractedFunction_compact a r hr.ne' hf).exists_cthickening_subset_open hS
    (contractedFunction_support_inside hS hconv ha hr hr1 hsupp)

theorem contractedFunction_continuous (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0)
    {f : SpatialCoordinates d → ℝ} (hf : Continuous f) :
    Continuous (contractedFunction a r hr f) :=
  hf.comp (centeredDilation a r hr).symm.continuous

theorem contractedFunction_hasFDerivAt (a : SpatialCoordinates d) (r : ℝ) (hr : r ≠ 0)
    {f : SpatialCoordinates d → ℝ} {x : SpatialCoordinates d}
    {A : SpatialCoordinates d →L[ℝ] ℝ}
    (hf : HasFDerivAt f A ((centeredDilation a r hr).symm x)) :
    HasFDerivAt (contractedFunction a r hr f) (A.comp (r⁻¹ • ContinuousLinearMap.id ℝ _)) x := by
  have hd : HasFDerivAt (fun y : SpatialCoordinates d => a + r⁻¹ • (y-a))
      (r⁻¹ • ContinuousLinearMap.id ℝ _) x := by
    simpa only [sub_zero,zero_add] using!
      (hasFDerivAt_const a x).add (((hasFDerivAt_id x).sub (hasFDerivAt_const a x)).const_smul r⁻¹)
  exact hf.comp x hd

end Carleman
