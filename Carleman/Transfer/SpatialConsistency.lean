module

public import Carleman.Periodic.OperatorEnergy

/-! Exact Section 4 consistency identities. All forms act on the actual
conforming reconstruction; Q=RJ and G=JR retain their original meanings.
The continuous variational equation is derived from the actual operator
equation, not assumed as an error estimate. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
namespace Orientation
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem difference_map (s : Orientation) (g : TimeGrid) (L : E →ₗ[ℝ] F)
    (u : g.Sequence E) : s.difference g (g.map L u) = g.map L (s.difference g u) := by
  cases s
  · exact g.dPlus_map L u
  · exact g.dMinus_map L u

theorem difference_sub (s : Orientation) (g : TimeGrid) (u v : g.Sequence E) :
    s.difference g (u - v) = s.difference g u - s.difference g v := by
  cases s
  · exact g.dPlus_sub u v
  · exact g.dMinus_sub u v

end Orientation
namespace Reconstruction
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {V : Submodule ℝ H} (r : Reconstruction V X)

/-- The original shifted form on V, independent of the norm used to present V. -/
def spatialForm (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (μ : ℝ) (v w : V) : ℝ :=
  a v w + μ * inner ℝ (v : H) (w : H)

theorem spatialForm_sub_left (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (μ : ℝ) (u v w : V) :
    spatialForm a μ (u-v) w = spatialForm a μ u w - spatialForm a μ v w := by
  simp only [spatialForm, map_sub, LinearMap.sub_apply, Submodule.coe_sub, inner_sub_left]
  ring

theorem spatialForm_sub_right (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (μ : ℝ) (u v w : V) :
    spatialForm a μ u (v-w) = spatialForm a μ u v - spatialForm a μ u w := by
  simp only [spatialForm, map_sub, Submodule.coe_sub, inner_sub_right]
  ring

/-- Original associated-operator testing converts the strong Euler equation
to the conforming variational equation, on the full original domain. -/
theorem spatial_continuous_test (g : TimeGrid) (s : Orientation)
    {D : Submodule ℝ H} (hDV : D ≤ V) (A : D →ₗ[ℝ] H)
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hA : ∀ (u : D) (v : V), inner ℝ (A u) (v : H) = a (Submodule.inclusion hDV u) v)
    (μ : g.Sequence ℝ) (f : g.Sequence H) (u : g.Sequence D)
    (hu : ∀ i, s.difference g (fun k => (u k : H)) i + A (u i) + μ i • (u i : H) = f i)
    (i : g.Index) (v : V) :
    inner ℝ (s.difference g (fun k => (u k : H)) i) (v : H) +
      spatialForm a (μ i) (Submodule.inclusion hDV (u i)) v = inner ℝ (f i) (v : H) := by
  have he := congrArg (fun z => inner ℝ z (v : H)) (hu i)
  simpa only [inner_add_left, real_inner_smul_left, hA, spatialForm, add_assoc,
    Submodule.coe_inclusion] using he

/-- Testing the actual auxiliary Euler scheme uses exactly N1's stiffness
identity and the mass-adjoint identity, without Q²=Q or G=Id. -/
theorem spatial_discrete_test (g : TimeGrid) (s : Orientation)
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A : X →ₗ[ℝ] X)
    (defect : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (hA : ∀ z v, inner ℝ (A z) v = a (r.R z) (r.R v) + defect z v)
    (μ : g.Sequence ℝ) (f : g.Sequence H) (z : g.Sequence X)
    (hz : ∀ i, s.difference g z i + A (z i) + μ i • r.G (z i) = r.J (f i))
    (i : g.Index) (v : X) :
    inner ℝ (s.difference g z i) v + spatialForm a (μ i) (r.R (z i)) (r.R v) +
      defect (z i) v = inner ℝ (f i) (r.R v : H) := by
  have he := congrArg (fun w => inner ℝ w v) (hz i)
  simp only [inner_add_left, real_inner_smul_left, hA, r.inner_G, r.mass_adjoint,
    RH_apply] at he
  dsimp only [spatialForm]
  linarith only [he]

/-- `eq:thetaEuler`: subtract the true Euler equations. The interpolation
error and stiffness defect remain explicit; no spatial error bound is input. -/
theorem spatial_error_equation (g : TimeGrid) (s : Orientation)
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A : X →ₗ[ℝ] X)
    (defect : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (hA : ∀ z v, inner ℝ (A z) v = a (r.R z) (r.R v) + defect z v)
    (μ : g.Sequence ℝ) (f : g.Sequence H) (u : g.Sequence V) (z : g.Sequence X)
    (hu : ∀ (i : g.Index) (v : V), inner ℝ (s.difference g (fun k => (u k : H)) i) (v : H) +
      spatialForm a (μ i) (u i) v = inner ℝ (f i) (v : H))
    (hz : ∀ i, s.difference g z i + A (z i) + μ i • r.G (z i) = r.J (f i))
    (i : g.Index) (v : X) :
    inner ℝ (s.difference g (fun k => z k - r.J (u k : H)) i) v +
      spatialForm a (μ i) (r.R (z i - r.J (u i : H))) (r.R v) +
      defect (z i - r.J (u i : H)) v =
      spatialForm a (μ i) (u i - r.Q (u i : H)) (r.R v) - defect (r.J (u i : H)) v := by
  have hd := r.spatial_discrete_test g s a A defect hA μ f z hz i v
  have hc := hu i (r.R v)
  have ht : s.difference g (fun k => z k - r.J (u k : H)) i =
      s.difference g z i - r.J (s.difference g (fun k => (u k : H)) i) := by
    change s.difference g (z - g.map r.J (fun k => (u k : H))) i = _
    rw [s.difference_sub, s.difference_map]
    rfl
  rw [ht, inner_sub_left, r.mass_adjoint, map_sub, spatialForm_sub_left,
    spatialForm_sub_left, map_sub, LinearMap.sub_apply, Q_apply]
  linarith only [hd, hc]

/-- Pointwise complete consistency identity before the periodic duality
step. This exposes separately the L² approximation, energy approximation
and stiffness-defect terms in `eq:completeidentity`. -/
theorem spatial_consistency_identity (g : TimeGrid) (s : Orientation)
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A : X →ₗ[ℝ] X)
    (defect : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (hA : ∀ z v, inner ℝ (A z) v = a (r.R z) (r.R v) + defect z v)
    (μ : g.Sequence ℝ) (f : g.Sequence H) (u : g.Sequence V) (z : g.Sequence X)
    (hu : ∀ (i : g.Index) (v : V), inner ℝ (s.difference g (fun k => (u k : H)) i) (v : H) +
      spatialForm a (μ i) (u i) v = inner ℝ (f i) (v : H))
    (hz : ∀ i, s.difference g z i + A (z i) + μ i • r.G (z i) = r.J (f i))
    (i : g.Index) (Y : V) :
    inner ℝ (s.difference g (fun k => (u k : H) - r.RH (z k)) i) (Y : H) +
      spatialForm a (μ i) (u i - r.R (z i)) Y =
      inner ℝ (s.difference g (fun k => (u k : H)) i) ((Y - r.Q (Y : H) : V) : H) +
      spatialForm a (μ i) (u i - r.R (z i)) (Y - r.Q (Y : H)) +
      defect (z i) (r.J (Y : H)) := by
  have hd := r.spatial_discrete_test g s a A defect hA μ f z hz i (r.J (Y : H))
  have hc := hu i (r.Q (Y : H))
  have ht : s.difference g (fun k => (u k : H) - r.RH (z k)) i =
      s.difference g (fun k => (u k : H)) i - r.RH (s.difference g z i) := by
    change s.difference g ((fun k => (u k : H)) - g.map r.RH z) i = _
    rw [s.difference_sub, s.difference_map]
    rfl
  rw [ht, inner_sub_left, r.inner_RH, spatialForm_sub_right,
    Submodule.coe_sub, inner_sub_right]
  simp only [spatialForm_sub_left, Q_apply] at hc ⊢
  linarith only [hd, hc]

end Reconstruction
end Carleman
