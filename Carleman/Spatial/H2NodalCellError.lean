module

public import Carleman.Spatial.H2NodalErrorJet

/-! The local nodal estimates now bound the actual error jet in the original
domain's L² classes. All Hessian energies remain on the same cell. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem nodalH2ErrorJet_cell_integral_bounds
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0)
    (hcont : ContinuousOn f (closure S)) (hfu : f =ᵐ[volume.restrict S] WeakSobolevJet.value u)
    (i : ι) {a : SpatialCoordinates d} {r D κ : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hball : Metric.ball a r ⊆ M.cell i) (hshape : D ≤ κ*r)
    (hdiam : ∀ x ∈ M.cell i, ∀ y ∈ M.cell i, dist x y ≤ D) :
    let e := M.nodalH2ErrorJet hS hM hB u f hf
    ((∫ x in M.cell i, (WeakSobolevJet.value e x)^2) ≤
      16*D^4*(tensorCoordinateBound d 2)^2*(d:ℝ)^2*
        (∫ x in M.cell i, ‖WeakSobolevJet.field 2 u x‖^2)) ∧
    ((∫ x in M.cell i, ‖WeakSobolevJet.field 1 e x‖^2) ≤
      ((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*D^2*
        (tensorCoordinateBound d 2)^2*(d:ℝ)^2*
          (∫ x in M.cell i, ‖WeakSobolevJet.field 2 u x‖^2)) := by
  let e := M.nodalH2ErrorJet hS hM hB u f hf
  have h0 := M.nodalH2ErrorJet_value_on_cell hS hc hM hB u f hf hfu i
  have h1 := M.nodalH2ErrorJet_gradient_on_cell hS hc hM hB u f hf i
  have hg := (zeroExtendLp_ae_restrict hS.measurableSet (WeakSobolevJet.field ⟨1,by omega⟩ u)).filter_mono
    (ae_mono (M.cell_measure_le_domain hS hc i))
  have hH := (zeroExtendLp_ae_restrict hS.measurableSet (WeakSobolevJet.field 2 u)).filter_mono
    (ae_mono (M.cell_measure_le_domain hS hc i))
  have heH : (∫ x in M.cell i, ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field 2 u) x‖^2)=
      ∫ x in M.cell i, ‖WeakSobolevJet.field 2 u x‖^2 :=
    integral_congr_ae (hH.mono fun x hx => by dsimp only; rw [hx])
  have he0 : (∫ x in M.cell i, (WeakSobolevJet.value e x)^2)=
      ∫ x in M.cell i, (f x-M.localNodal f i x)^2 :=
    integral_congr_ae (h0.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
  have he1 : (∫ x in M.cell i, ‖WeakSobolevJet.field 1 e x‖^2)=
      ∫ x in M.cell i, ‖zeroExtendLp hS.measurableSet (WeakSobolevJet.field ⟨1,by omega⟩ u) x-
        derivativeOneFiber (affineScalarDerivative (M.localNodal f i))‖^2 := by
    apply integral_congr_ae
    filter_upwards [h1,hg] with x hx hy
    rw [hx,hy]
  have hb0 := WeakSobolevJet.simplex_nodal_value_integral hS hc hb hd u hcont hfu
    (M.simplex i) (M.inside i) hD hdiam
  have hb1 := WeakSobolevJet.simplex_nodal_gradient_integral hS hc hb hd u hcont hfu
    (M.simplex i) (M.inside i) hr hD hball hshape hdiam
  rw [heH] at hb0 hb1
  constructor
  · rw [he0]
    exact hb0
  · rw [he1]
    exact hb1

end Carleman.SimplicialPartition
