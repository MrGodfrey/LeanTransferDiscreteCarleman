module

public import Carleman.Transfer.SobolevFiniteness
public import Carleman.Spatial.SobolevTruncation
public import Carleman.Transfer.ErrorBridge
public import Carleman.Transfer.ShiftNorm
public import Carleman.Transfer.SobolevGeometry

/-! Assemble the concrete B3 bridge. Every weighted finiteness field follows
from A1 and the genuine B1 trajectory. Only the original nodal bounds, A4,
and the still-unproved frozen solution remain as inputs. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {a : CarlemanExponents} {V : Submodule ℝ (Lp ℝ 2 ν)}
  (hV : V ≤ sobolevSubspace d a.m ν S)
  {X F Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  {Z : Fin a.m → Type*} [∀ j, NormedAddCommGroup (Z j)]
  [∀ j, InnerProductSpace ℝ (Z j)]
  (w : TimeWeight) (ρ : SpatialProfile ν)
  (P : ∀ j : Fin a.m, DifferentialExpression ν
      (fun k : Fin (a.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
  (hstate : ∀ t v, state t v = 0 → v = 0)
  (hload : ∀ t v, load t v = 0 → v = 0)
  (hcontrol : ∀ t v, control t v = 0 → v = 0)

local notation "p" => sobolevGeometry hS hν hV w ρ P obs hobs state load control hstate hload hcontrol

variable [SFinite ν] {g : TimeGrid} {β : ℝ}
  (hq : TimeWeightRegularity w g β)
  {D : Submodule ℝ (Lp ℝ 2 ν)} {A : D →ₗ[ℝ] Lp ℝ 2 ν}
  (hDV : D ≤ V) (hD : D ≤ sobolevSubspace d (2*a.m) ν S)
  (Creg : ℝ) (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖A v‖)
  (r : Reconstruction V X) (l : LoadInterface r F) (Bstar : X →ₗ[ℝ] Y)
  (s : Orientation) (μ : g.Sequence ℝ) (f : g.Sequence F) (z : g.Sequence X)
  (u : PeriodicWeakTrajectory g D A)

include hq hD Creg hell in
/-- Actual B3 and all its finite-density obligations, for both orientations
and all discrete states. K merely dominates the original uniform constants. -/
theorem sobolevGeometry_comparisonBridge
    (hm : g.dt*w.max^2 ≤ cellThreshold β a.comparisonExponent ρ.bound)
    (Cstate Cload Cobs K : ℝ) (hCs : 0 ≤ Cstate)
    (hK9 : 9 ≤ K) (hKs : 9*Cstate ≤ K) (hKl : 9*Cload ≤ K) (hKo : 9*Cobs ≤ K)
    (hnode : ∀ i, (state (g.nodeTime i) (z i))^2 ≤
      Cstate*((ρ.multiplier w 0 (g.nodeTime i)).seminorm (r.RH (z i)))^2)
    (hlift : ∀ i, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (l.lift (f i)))^2 ≤
      Cload*(load (g.nodeTime i) (f i))^2)
    (hobserve : ∀ i, ((ρ.multiplier w 0 (g.nodeTime i)).observation obs hobs (r.RH (z i)))^2 ≤
      Cobs*(control (g.nodeTime i) (Bstar (z i)))^2)
    (hfrozen : ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + A (u.domainValue t) + s.extension g μ t • u.value t =
        s.extension g (l.transferLoad g μ f z) t)
    (hcarleman : (p).continuousEnergy g ((p).trajectory g hDV u) ≤ K *
      (timeSq g w.q 0 (p).space (fun t => s.sign • u.derivative t + A (u.domainValue t)) +
       timeSq g w.q a.o (p).observation (fun t => (u.domainValue t : Lp ℝ 2 ν)))) :
    ComparisonBridge (p) g r l A hDV Bstar s μ f z u K := by
  have hel := elliptic_bound_lower_order hS hν (m := a.m) (n := 2*a.m)
    (by omega) (hDV.trans hV) hD A Creg hell
  have hU := sobolevGeometry_trajectory_graph_L2 hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol hDV u Creg hel
  have hR := sobolevGeometry_reconstruction_graph_L2 hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol r s z
  have hE := sobolevGeometry_error_graph_L2 hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol hDV u Creg hel r s z
  have heH := conforming_value_L2 hS hν hV hE
  have hrH := conforming_value_L2 hS hν hV hR
  have hcmp := sobolevGeometry_comparisons hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol hq r hm l.lift Bstar Cstate Cload Cobs hCs s z f hnode hlift hobserve
  have finiteH := sobolevGeometry_value_finite hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol hq.aestronglyMeasurable
  have finiteO := sobolevGeometry_observation_finite hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol hq.aestronglyMeasurable
  have finiteD := sobolevGeometry_derivative_finite hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol hq.aestronglyMeasurable
  refine {
    frozen := hfrozen
    carleman := hcarleman
    node_state := hcmp.2.1.trans (mul_le_mul_of_nonneg_right hKs (timeSq_nonneg g w.q w.nonneg _ _ _))
    node_derivative := fun j => (hcmp.1 j).2.trans
      (mul_le_mul_of_nonneg_right hK9 (timeSq_nonneg g w.q w.nonneg _ _ _))
    lifted_load := hcmp.2.2.1.trans
      (mul_le_mul_of_nonneg_right hKl (g.weightedSq_nonneg _ _))
    observed_reconstruction := hcmp.2.2.2.trans
      (mul_le_mul_of_nonneg_right hKo (g.powerSq_nonneg _ (fun _ => w.nonneg _) _ _ _))
    finite_residual := finiteH 0 ((u.derivative_L2.const_smul s.sign).add u.operator_L2)
    finite_observed_value := finiteO a.o u.domainValue_L2
    finite_reconstruction₀ := finiteH a.c₀ hrH
    finite_reconstructionD := fun j => (hcmp.1 j).1
    finite_value₀ := finiteH a.c₀ u.domainValue_L2
    finite_error₀ := finiteH a.c₀ heH
    finite_valueD := fun j => finiteD (a.c j) hU j
    finite_errorD := fun j => finiteD (a.c j) hE j
    finite_lift := finiteH 0 (s.memLp_extension g _)
    finite_shift := finiteH 0 (s.memLp_smul_extension g μ heH)
    finite_observed_reconstruction := finiteO a.o hrH
    finite_observed_error := finiteO a.o heH.neg }

omit Bstar μ [SFinite ν] in
include hq hD Creg hell in
/-- In B4 only the substantive energy and L² error estimates remain inputs.
Order, frozen shift and every weighted finiteness field are proved here. -/
theorem sobolevGeometry_errorBridge (Ah : X →ₗ[ℝ] X) (L : ℝ) (hL : 0 ≤ L)
    (hm : β*g.dt*w.max^2 ≤ 1/2) (errors : ErrorScales) (K τ : ℝ)
    (hKD : differentialFamilyBound P ≤ K) (hKL : (2*L)^(4*a.m) ≤ K)
    (henergy : s.difference g z + r.shiftedSpatial g Ah (frozenShift a w g L) z =
        g.map r.J (l.transferLoad g (frozenShift a w g L) f z) →
      ∀ j, a.energyPower j / 2 ≤ τ →
        (p).graphSq g (a.energyPower j) ((p).error g hDV u r s z) ≤
          K * errors.energy g ^ 2 * g.powerSq (w.nodes g) (a.energyPower j)
            ((p).node g (p).space) (l.transferLoad g (frozenShift a w g L) f z))
    (hl2 : s.difference g z + r.shiftedSpatial g Ah (frozenShift a w g L) z =
        g.map r.J (l.transferLoad g (frozenShift a w g L) f z) →
      ∀ b, b = a.c₀ ∨ b = a.o ∨ b = (4*a.m : ℝ) → b/2 ≤ τ →
        timeSq g w.q b (p).space (fun t => ((p).error g hDV u r s z t : Lp ℝ 2 ν)) ≤
          K * errors.l2 g ^ 2 * g.powerSq (w.nodes g) b
            ((p).node g (p).space) (l.transferLoad g (frozenShift a w g L) f z)) :
    ErrorBridge (p) g r l A Ah hDV s (frozenShift a w g L) f z u errors K τ := by
  have hel := elliptic_bound_lower_order hS hν (m := a.m) (n := 2*a.m)
    (by omega) (hDV.trans hV) hD A Creg hell
  have hE := sobolevGeometry_error_graph_L2 hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol hDV u Creg hel r s z
  have heH := conforming_value_L2 hS hν hV hE
  have hfinite (b : ℝ) := sobolevGeometry_value_finite hS hν hV w ρ P obs hobs state load control
    hstate hload hcontrol hq.aestronglyMeasurable b heH
  have hgraph (j : Fin a.m) (k : Fin (a.m+1)) :=
    sobolevGeometry_gradient_finite hS hν hV w ρ P obs hobs state load control
      hstate hload hcontrol hq.aestronglyMeasurable
      (2*(a.m-k.val : ℕ)+a.energyPower j) hE k
  refine {
    energy := henergy
    l2 := hl2
    finite_l2 := fun b _ => hfinite b
    finite_energy := hgraph
    order := ?_
    shift := ?_ }
  · intro j
    exact (sobolevGeometry_order hS hν hV w ρ P obs hobs state load control
      hstate hload hcontrol g _ hgraph j).trans
      (mul_le_mul_of_nonneg_right hKD
        (Finset.sum_nonneg fun k _ => timeSq_nonneg g w.q w.nonneg _ _ _))
  · exact (frozenShift_timeSq_le hq a s L hL hm (p).space _ (hfinite (4*a.m))).2.trans
      (mul_le_mul_of_nonneg_right hKL (timeSq_nonneg g w.q w.nonneg _ _ _))

end Carleman
