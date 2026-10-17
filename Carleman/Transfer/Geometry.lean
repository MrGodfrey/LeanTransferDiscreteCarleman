module

public import Carleman.Transfer.LoadBound

/-!
# Normed objects in Section 5

Spatially weighted norms are supplied by the discretization, exactly as in
Section 2. They are seminorms with definiteness recorded for H, X, F and the
control space Y; observations and differential expressions can have kernels.
`derivative j t v` means ‖θ(t) 𝒟_{j+1}v‖, and `gradient k t v` means
‖θ(t) D^k v‖. Their order relation is an explicit bridge below, never inferred
merely from these names. These are functions of the actual reconstructed and
continuous states, not independent scalar energies. Concrete spatial/PDE
realizations remain part of the downstream manuscript assumptions.
-/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {H X F Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]

structure TransferGeometry (V : Submodule ℝ H) (X F Y : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
    (a : CarlemanExponents) where
  weight : TimeWeight
  state : ℝ → Seminorm ℝ X
  load : ℝ → Seminorm ℝ F
  control : ℝ → Seminorm ℝ Y
  space : ℝ → Seminorm ℝ H
  observation : ℝ → Seminorm ℝ H
  derivative : Fin a.m → ℝ → Seminorm ℝ V
  gradient : Fin (a.m + 1) → ℝ → Seminorm ℝ V
  state_definite : ∀ t x, state t x = 0 → x = 0
  load_definite : ∀ t x, load t x = 0 → x = 0
  control_definite : ∀ t x, control t x = 0 → x = 0
  space_definite : ∀ t x, space t x = 0 → x = 0
  observation_le : ∀ t x, observation t x ≤ space t x
  gradient_zero : ∀ t v, gradient 0 t v = space t (v : H)

namespace TransferGeometry
variable {V : Submodule ℝ H} {a : CarlemanExponents}
  (p : TransferGeometry V X F Y a) (g : TimeGrid)

def node (_p : TransferGeometry V X F Y a) (g : TimeGrid) {E : Type*} [AddCommGroup E] [Module ℝ E] (s : ℝ → Seminorm ℝ E) :
    g.Index → Seminorm ℝ E := fun i => s (g.nodeTime i)

def nodeEnergy (r : Reconstruction V X) (z : g.Sequence X) : ℝ :=
  g.powerSq (p.weight.nodes g) a.c₀ (p.node g p.state) z +
    ∑ j, g.powerSq (p.weight.nodes g) (a.c j) (p.node g (p.derivative j)) (fun i => r.R (z i))

def continuousEnergy (u : ℝ → V) : ℝ :=
  timeSq g p.weight.q a.c₀ p.space (fun t => (u t : H)) +
    ∑ j, timeSq g p.weight.q (a.c j) (p.derivative j) u

def graphSq (s : ℝ) (u : ℝ → V) : ℝ :=
  ∑ k : Fin (a.m + 1), timeSq g p.weight.q
    (2 * (a.m - k.val : ℕ) + s) (p.gradient k) u

def loadSq (f : g.Sequence F) : ℝ := g.weightedSq (p.node g p.load) f

def observationSq (Bstar : X →ₗ[ℝ] Y) (z : g.Sequence X) : ℝ :=
  g.powerSq (p.weight.nodes g) a.o (p.node g p.control) (fun i => Bstar (z i))

def reconstruction (_p : TransferGeometry V X F Y a) (g : TimeGrid) (r : Reconstruction V X) (s : Orientation) (z : g.Sequence X) : ℝ → V :=
  fun t => r.R (s.extension g z t)

def trajectory (_p : TransferGeometry V X F Y a) (g : TimeGrid) {D : Submodule ℝ H} {A : D →ₗ[ℝ] H} (hDV : D ≤ V)
    (u : PeriodicWeakTrajectory g D A) : ℝ → V :=
  fun t => D.inclusion hDV (u.domainValue t)

def error {D : Submodule ℝ H} {A : D →ₗ[ℝ] H} (hDV : D ≤ V)
    (u : PeriodicWeakTrajectory g D A) (r : Reconstruction V X)
    (s : Orientation) (z : g.Sequence X) : ℝ → V :=
  p.trajectory g hDV u - p.reconstruction g r s z

/-- The actual derivative error sum, before using B4. -/
def derivativeError (e : ℝ → V) : ℝ :=
  ∑ j, timeSq g p.weight.q (a.c j) (p.derivative j) e

def lowerErrors (s : Orientation) (μ : g.Sequence ℝ) (e : ℝ → V) : ℝ :=
  timeSq g p.weight.q a.c₀ p.space (fun t => (e t : H)) +
  timeSq g p.weight.q a.o p.observation (fun t => (e t : H)) +
  timeSq g p.weight.q 0 p.space (fun t => s.extension g μ t • (e t : H))

omit [CompleteSpace H] in
theorem nodeEnergy_nonneg (r : Reconstruction V X) (z : g.Sequence X) :
    0 ≤ p.nodeEnergy g r z := by
  apply add_nonneg (g.powerSq_nonneg _ (fun _ => p.weight.nonneg _) _ _ _)
  exact Finset.sum_nonneg fun _ _ => g.powerSq_nonneg _ (fun _ => p.weight.nonneg _) _ _ _

omit [CompleteSpace H] in
theorem zeroth_le_nodeEnergy (r : Reconstruction V X) (z : g.Sequence X) :
    g.powerSq (p.weight.nodes g) a.c₀ (p.node g p.state) z ≤ p.nodeEnergy g r z := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun _ _ => g.powerSq_nonneg _ (fun _ => p.weight.nonneg _) _ _ _

end TransferGeometry
end Carleman

@[expose] public noncomputable section
namespace Carleman.TransferGeometry
open scoped BigOperators
variable {H X F Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  {V : Submodule ℝ H} {a : CarlemanExponents}
  (p : TransferGeometry V X F Y a) (g : TimeGrid)

omit [CompleteSpace H] in
theorem continuousEnergy_sub_le (u v : ℝ → V)
    (hu₀ : TimeSquareIntegrable g p.weight.q a.c₀ p.space (fun t => (u t : H)))
    (hv₀ : TimeSquareIntegrable g p.weight.q a.c₀ p.space (fun t => (v t : H)))
    (huD : ∀ j, TimeSquareIntegrable g p.weight.q (a.c j) (p.derivative j) u)
    (hvD : ∀ j, TimeSquareIntegrable g p.weight.q (a.c j) (p.derivative j) v) :
    p.continuousEnergy g (u - v) ≤ 2 * (p.continuousEnergy g u + p.continuousEnergy g v) := by
  have h₀ := timeSq_sub_le g p.weight.q p.weight.nonneg a.c₀ p.space
    (fun t => (u t : H)) (fun t => (v t : H)) hu₀ hv₀
  have hD := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    timeSq_sub_le g p.weight.q p.weight.nonneg (a.c j) (p.derivative j) u v (huD j) (hvD j)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hD
  change _ + _ ≤ _
  dsimp only [continuousEnergy]
  have heq : (fun t => ((u - v) t : H)) = (fun t => (u t : H)) - (fun t => (v t : H)) := rfl
  rw [heq]
  linarith

end Carleman.TransferGeometry
