module

public import Carleman.Spatial.SobolevRealization
public import Carleman.Transfer.DifferentialOrder
public import Carleman.Transfer.ConcreteNorms

/-!
# A concrete Sobolev realization of TransferGeometry

H is the actual scalar L² space, V is any linear conforming subspace of the
weak H^m space constructed above, and each D_j is the actual finite expression
of order at most j with bounded spatial coefficients. Numerical X/load/control
norms are left as the original numerical data. No energy estimate is assumed.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
/-- This enlargement is only for temporal cell analysis; it does not enlarge
the numerical allowed-weight family in N1--N5. -/
def CarlemanExponents.comparisonExponent (a : CarlemanExponents) : ℝ :=
  a.c₀/2 + a.o/2 + ∑ j, a.c j/2

theorem CarlemanExponents.comparisonExponent_bounds (a : CarlemanExponents) :
    0 ≤ a.comparisonExponent ∧ |a.c₀/2| ≤ a.comparisonExponent ∧
      |a.o/2| ≤ a.comparisonExponent ∧ ∀ j, |a.c j/2| ≤ a.comparisonExponent := by
  have hs : 0 ≤ ∑ j, a.c j/2 := Finset.sum_nonneg fun j _ => div_nonneg (a.c_nonneg j) (by norm_num)
  have hc := a.c₀_pos
  have ho := a.o_nonneg
  refine ⟨by dsimp [comparisonExponent]; positivity, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg (by positivity)]
    dsimp [comparisonExponent]; linarith
  · rw [abs_of_nonneg (by positivity)]
    dsimp [comparisonExponent]; linarith
  · intro j
    rw [abs_of_nonneg (div_nonneg (a.c_nonneg j) (by norm_num))]
    have hj := Finset.single_le_sum (s := Finset.univ)
      (fun k _ => div_nonneg (a.c_nonneg k) (by norm_num : (0:ℝ) ≤ 2)) (Finset.mem_univ j)
    dsimp [comparisonExponent]; linarith

variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {a : CarlemanExponents} {V : Submodule ℝ (Lp ℝ 2 ν)}
  (hV : V ≤ sobolevSubspace d a.m ν S)

/-- The genuine weak spatial derivative field of a conforming state. -/
def conformingDerivative (k : Fin (a.m+1)) : V →ₗ[ℝ] Lp (DerivativeFiber d k.val) 2 ν :=
  (sobolevDerivative hS hν k).comp (V.inclusion hV)

def conformingExpression {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (j : Fin a.m)
    (D : DifferentialExpression ν (fun k : Fin (a.m+1) => DerivativeFiber d k.val) Z (j.val+1)) :
    V →ₗ[ℝ] Lp Z 2 ν := D.onFields (conformingDerivative hS hν hV)

theorem conformingDerivative_zero_seminorm (w : BoundedMultiplier ν) (v : V) :
    w.seminorm (conformingDerivative hS hν hV 0 v) = w.seminorm (v : Lp ℝ 2 ν) :=
  sobolevDerivative_zero_seminorm hS hν w (V.inclusion hV v)

/-- The conforming fields satisfy the actual coordinate weak derivative identity. -/
theorem conformingDerivative_weak (v : V) (k : Fin a.m)
    (α : Sym (Fin d) k.val) (i : Fin d) :
    IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i)
      (derivativeComponent α (conformingDerivative hS hν hV k.castSucc v))
      (derivativeComponent (Sym.cons i α) (conformingDerivative hS hν hV k.succ v)) :=
  sobolevDerivative_weak hS hν (V.inclusion hV v) k α i

/-- The expression is exactly the sum of its pointwise coefficient actions
on canonical weak derivative collections, also for vector-valued outputs. -/
theorem conformingExpression_ae {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (j : Fin a.m)
    (D : DifferentialExpression ν (fun k : Fin (a.m+1) => DerivativeFiber d k.val) Z (j.val+1))
    (v : V) :
    conformingExpression hS hν hV j D v =ᵐ[ν]
      (fun x => ∑ k ∈ D.orders,
        (D.coefficient k).value x (conformingDerivative hS hν hV k v x)) :=
  D.apply_ae (fun k => conformingDerivative hS hν hV k v)

variable {Z : Fin a.m → Type*} [∀ j, NormedAddCommGroup (Z j)]
  [∀ j, InnerProductSpace ℝ (Z j)]
variable {X F Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]

/-- Spatial realization of every norm field, with the original numerical norm
families and their definiteness as data. No derivative-order inequality occurs
among the inputs. -/
def sobolevGeometry (w : TimeWeight) (ρ : SpatialProfile ν)
    (D : ∀ j : Fin a.m, DifferentialExpression ν
      (fun k : Fin (a.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
    (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
    (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
    (hstate : ∀ t v, state t v = 0 → v = 0)
    (hload : ∀ t v, load t v = 0 → v = 0)
    (hcontrol : ∀ t v, control t v = 0 → v = 0) : TransferGeometry V X F Y a where
  weight := w
  state := state
  load := load
  control := control
  space t := (ρ.multiplier w 0 t).seminorm
  observation t := (ρ.multiplier w 0 t).observation obs hobs
  derivative j t := (ρ.multiplier w 0 t).seminorm.comp (conformingExpression hS hν hV j (D j))
  gradient k t := (ρ.multiplier w 0 t).seminorm.comp (conformingDerivative hS hν hV k)
  state_definite := hstate
  load_definite := hload
  control_definite := hcontrol
  space_definite t v := (ρ.seminorm_definite w 0 t v).mp
  observation_le t v := (ρ.multiplier w 0 t).observation_le obs hobs v
  gradient_zero t v := conformingDerivative_zero_seminorm hS hν hV (ρ.multiplier w 0 t) v

end Carleman

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
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
  (D : ∀ j : Fin a.m, DifferentialExpression ν
      (fun k : Fin (a.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
  (hstate : ∀ t v, state t v = 0 → v = 0)
  (hload : ∀ t v, load t v = 0 → v = 0)
  (hcontrol : ∀ t v, control t v = 0 → v = 0)

/-- One explicit constant for every expression j; it depends only on fixed
spatial coefficients and the order, never on T, h, delta t, q, or the state. -/
def differentialFamilyBound : ℝ :=
  1 + ∑ j : Fin a.m, (D j).boundSq

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
theorem differentialFamilyBound_ge_one : 1 ≤ differentialFamilyBound D :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => DifferentialExpression.boundSq_nonneg _)

local notation "p" => sobolevGeometry hS hν hV w ρ D obs hobs state load control hstate hload hcontrol

/-- B4-order is a theorem for this concrete Sobolev geometry. Only the graph
integrals already required by B4 finite_energy are inputs. -/
theorem sobolevGeometry_order (g : TimeGrid) (u : ℝ → V)
    (hf : ∀ (j : Fin a.m) (k : Fin (a.m+1)), TimeSquareIntegrable g w.q
      (2*(a.m-k.val : ℕ)+a.energyPower j) ((p).gradient k) u) (j : Fin a.m) :
    timeSq g w.q (a.c j) ((p).derivative j) u ≤
      differentialFamilyBound D * (p).graphSq g (a.energyPower j) u := by
  have hh := (p).order_of_L2_expression ρ g j (D j)
    (conformingDerivative hS hν hV) (fun _ => rfl) rfl u (hf j)
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · have hs := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => (D j).boundSq_nonneg)
      (Finset.mem_univ j)
    change _ ≤ 1 + _
    linarith
  · exact Finset.sum_nonneg fun k _ => timeSq_nonneg g w.q w.nonneg _ _ _

variable [SFinite ν] {g : TimeGrid} {β : ℝ}
  (hq : TimeWeightRegularity w g β) (r : Reconstruction V X)
include hq

/-- The B3 derivative comparison and its finiteness now use the canonical
Sobolev fields, without a derivative-field identification premise. -/
theorem sobolevGeometry_node_derivative (j : Fin a.m) (τStar : ℝ)
    (hτ : |a.c j/2| ≤ τStar) (hm : β*g.dt*w.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound))*g.dt*w.max^2 ≤ 1)
    (s : Orientation) (z : g.Sequence X) :
    TimeSquareIntegrable g w.q (a.c j) ((p).derivative j) ((p).reconstruction g r s z) ∧
      g.powerSq (w.nodes g) (a.c j) ((p).node g ((p).derivative j)) (fun i => r.R (z i)) ≤
        9*timeSq g w.q (a.c j) ((p).derivative j) ((p).reconstruction g r s z) :=
  (p).node_derivative_of_L2 ρ hq r j (conformingExpression hS hν hV j (D j)) 0 τStar rfl
    (by simpa only [zero_add] using hτ) hm hmw s z

/-- The original N1 nodal state lower bound and proved time comparison. -/
theorem sobolevGeometry_node_state (τStar C : ℝ) (hC : 0 ≤ C)
    (hτ : |a.c₀/2| ≤ τStar) (hm : β*g.dt*w.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound))*g.dt*w.max^2 ≤ 1)
    (s : Orientation) (z : g.Sequence X)
    (hn : ∀ i, (state (g.nodeTime i) (z i))^2 ≤
      C*((ρ.multiplier w 0 (g.nodeTime i)).seminorm (r.RH (z i)))^2) :
    g.powerSq (w.nodes g) a.c₀ ((p).node g (p).state) z ≤
      (9*C)*timeSq g w.q a.c₀ (p).space (fun t => r.RH (s.extension g z t)) :=
  (p).node_state_of_L2 ρ hq r (LinearMap.id) 0 τStar C hC rfl
    (by simpa only [zero_add] using hτ) hm hmw s z hn

omit r in
/-- The original N2 bound for the ordinary lift, with the actual H norm. -/
theorem sobolevGeometry_lifted_load (lift : F → Lp ℝ 2 ν) (τStar C : ℝ)
    (hτ : 0 ≤ τStar) (hm : β*g.dt*w.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound))*g.dt*w.max^2 ≤ 1)
    (s : Orientation) (f : g.Sequence F)
    (hn : ∀ i, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (lift (f i)))^2 ≤
      C*(load (g.nodeTime i) (f i))^2) :
    timeSq g w.q 0 (p).space (s.extension g (fun i => lift (f i))) ≤ (9*C)*(p).loadSq g f :=
  (p).lifted_load_of_L2 ρ hq (LinearMap.id) lift 0 τStar C rfl
    (by simpa only [abs_zero] using hτ) hm hmw s f hn

/-- The N5 observation input is measured on the actual observation region. -/
theorem sobolevGeometry_observation (Bstar : X →ₗ[ℝ] Y) (τStar C : ℝ)
    (hτ : |a.o/2| ≤ τStar) (hm : β*g.dt*w.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound))*g.dt*w.max^2 ≤ 1)
    (s : Orientation) (z : g.Sequence X)
    (hn : ∀ i, ((ρ.multiplier w 0 (g.nodeTime i)).observation obs hobs (r.RH (z i)))^2 ≤
      C*(control (g.nodeTime i) (Bstar (z i)))^2) :
    timeSq g w.q a.o (p).observation (fun t => r.RH (s.extension g z t)) ≤
      (9*C)*(p).observationSq g Bstar z :=
  (p).observed_reconstruction_of_L2 ρ hq r (BoundedMultiplier.cutoff obs hobs).linearMap
    Bstar 0 τStar C rfl (by simpa only [zero_add] using hτ) hm hmw s z hn
/-- All temporal B3 comparison fields for the concrete Sobolev geometry,
from a single explicit threshold independent of T and the time grid. The only
spatial inequalities are precisely the original numerical N1, N2 and N5 bounds. -/
theorem sobolevGeometry_comparisons
    (hm : g.dt*w.max^2 ≤ cellThreshold β a.comparisonExponent ρ.bound)
    (lift : F → Lp ℝ 2 ν) (Bstar : X →ₗ[ℝ] Y)
    (Cstate Cload Cobs : ℝ) (hCstate : 0 ≤ Cstate)
    (s : Orientation) (z : g.Sequence X) (f : g.Sequence F)
    (hnode : ∀ i, (state (g.nodeTime i) (z i))^2 ≤
      Cstate*((ρ.multiplier w 0 (g.nodeTime i)).seminorm (r.RH (z i)))^2)
    (hlift : ∀ i, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (lift (f i)))^2 ≤
      Cload*(load (g.nodeTime i) (f i))^2)
    (hobserve : ∀ i, ((ρ.multiplier w 0 (g.nodeTime i)).observation obs hobs (r.RH (z i)))^2 ≤
      Cobs*(control (g.nodeTime i) (Bstar (z i)))^2) :
    (∀ j, TimeSquareIntegrable g w.q (a.c j) ((p).derivative j) ((p).reconstruction g r s z) ∧
      g.powerSq (w.nodes g) (a.c j) ((p).node g ((p).derivative j)) (fun i => r.R (z i)) ≤
        9*timeSq g w.q (a.c j) ((p).derivative j) ((p).reconstruction g r s z)) ∧
    g.powerSq (w.nodes g) a.c₀ ((p).node g (p).state) z ≤
      (9*Cstate)*timeSq g w.q a.c₀ (p).space (fun t => r.RH (s.extension g z t)) ∧
    timeSq g w.q 0 (p).space (s.extension g (fun i => lift (f i))) ≤ (9*Cload)*(p).loadSq g f ∧
    timeSq g w.q a.o (p).observation (fun t => r.RH (s.extension g z t)) ≤
      (9*Cobs)*(p).observationSq g Bstar z := by
  have he := a.comparisonExponent_bounds
  have hb := hq.mesh_bounds a.comparisonExponent ρ.bound he.1 ρ.bound_nonneg hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    exact sobolevGeometry_node_derivative hS hν hV w ρ D obs hobs state load control
      hstate hload hcontrol hq r j _ (he.2.2.2 j) hb.1 hb.2 s z
  · exact sobolevGeometry_node_state hS hν hV w ρ D obs hobs state load control
      hstate hload hcontrol hq r _ Cstate hCstate he.2.1 hb.1 hb.2 s z hnode
  · exact sobolevGeometry_lifted_load hS hν hV w ρ D obs hobs state load control
      hstate hload hcontrol hq lift _ Cload he.1 hb.1 hb.2 s f hlift
  · exact sobolevGeometry_observation hS hν hV w ρ D obs hobs state load control
      hstate hload hcontrol hq r Bstar _ Cobs he.2.2.1 hb.1 hb.2 s z hobserve

end Carleman
