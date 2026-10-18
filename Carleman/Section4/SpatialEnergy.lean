module

public import Carleman.Transfer.SpatialCea
public import Carleman.Transfer.WeightedTestTime
public import Carleman.Spatial.SquaredWeightTest
public import Carleman.Section3.OriginalForm

/-! Section 4's Cea estimate on the original weak Sobolev space. A3 supplies
the shifted form bounds, N1 the exact stiffness defect and N4 the genuine
test family. The time margin is discharged by the actual allowed weight.
The approximation and Euler graph bounds are composed in the next layer. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
namespace OriginalForm
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}

/-- Bundle the same original scalar form for the exact consistency identities. -/
def bilinearForm (a : OriginalForm (m := m) hS hν) : a.V →ₗ[ℝ] a.V →ₗ[ℝ] ℝ :=
  a.form.toLinearMap₁₂.compl₁₂ a.valueEquiv.symm.toLinearMap a.valueEquiv.symm.toLinearMap

theorem bilinearForm_apply (a : OriginalForm (m := m) hS hν) (u v : a.V) :
    a.bilinearForm u v = a.scalarForm u v := rfl

end OriginalForm
namespace Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (r : Reconstruction V X) (g : TimeGrid) (s : Orientation)
  (ρ : SpatialProfile ν) (w : TimeWeight)

/-- The norm used below is exactly the original Nσ,δt, via its established
seminorm realization. No H-induced norm is substituted for H^m. -/
def energySeminorm (τ : ℝ) (i : g.Index) : Seminorm ℝ V :=
  conformingWeightedSeminorm hS hν hV (w.q (g.nodeTime i)) (ρ.multiplier w τ (g.nodeTime i))

/-- The reconstructed discrete-error estimate with explicit constants.
The two solution equations are the actual continuous and discrete Euler
problems; the Cea error equation and time lower bound are derived here. -/
theorem spatial_cea (β τ τStar : ℝ) (h : TimeWeightRegularity w g β) (hτ : |τ| ≤ τStar)
    (hm : β*g.dt*w.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound))*g.dt*w.max^2 ≤ 1)
    (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A : X →ₗ[ℝ] X) (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (hA : ∀ z v, inner ℝ (A z) v = a (r.R z) (r.R v)+b z v)
    (μ : g.Sequence ℝ) (T T' : ℝ → X →ₗ[ℝ] X) (hend : T 0 = T g.period)
    (hder : ∀ z t, t ∈ Icc 0 g.period →
      HasDerivWithinAt (fun x => inner ℝ z (T x z)) (inner ℝ z (T' t z)) (Icc 0 g.period) t)
    (hsym : ∀ i v z, inner ℝ v (T (g.nodeTime i) z) = inner ℝ z (T (g.nodeTime i) v))
    (hpos : ∀ i z, 0 ≤ inner ℝ z (T (g.nodeTime i) z))
    (hw : ∀ t (v : V), (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V)
    {c Cf Ctime CM ε ηA : ℝ} (hc : 0 < c) (hCf : 0 ≤ Cf) (hCtime : 0 ≤ Ctime)
    (hCM : 0 ≤ CM) (hε : 0 ≤ ε) (hηA : 0 ≤ ηA)
    (htime : ∀ z t, t ∈ Icc 0 g.period →
      |inner ℝ z (T' t z)| ≤ Ctime*(w.q t*(ρ.multiplier w τ t).seminorm (r.RH z))^2)
    (hform : ∀ i v z, |Reconstruction.spatialForm a (μ i) v z| ≤
      Cf*conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.multiplier w τ (g.nodeTime i)) v*
        conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.neg.multiplier w (-τ) (g.nodeTime i)) z)
    (hcoer : ∀ i v, c*(conformingWeightedNorm hS hν hV (w.q (g.nodeTime i))
        (ρ.multiplier w τ (g.nodeTime i)) v)^2+
      (18*Ctime)*(w.q (g.nodeTime i)*(ρ.multiplier w τ (g.nodeTime i)).seminorm (v : Lp ℝ 2 ν))^2 ≤
      Reconstruction.spatialForm a (μ i) v
        (conformingWeight (ρ.multiplier w τ (g.nodeTime i)) (hw _) (conformingWeight
          (ρ.multiplier w τ (g.nodeTime i)) (hw _) v)))
    (hdefect : ∀ i z v, |b z v| ≤
      ηA*conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.multiplier w τ (g.nodeTime i)) (r.R z)*
        conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.neg.multiplier w (-τ) (g.nodeTime i)) (r.R v))
    (hmul : ∀ i v, conformingWeightedNorm hS hν hV (w.q (g.nodeTime i))
      (ρ.neg.multiplier w (-τ) (g.nodeTime i))
        (conformingWeight (ρ.multiplier w τ (g.nodeTime i)) (hw _) (conformingWeight
          (ρ.multiplier w τ (g.nodeTime i)) (hw _) v)) ≤
      CM*conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.multiplier w τ (g.nodeTime i)) v)
    (hsuper : ∀ i z, conformingWeightedNorm hS hν hV (w.q (g.nodeTime i))
      (ρ.neg.multiplier w (-τ) (g.nodeTime i))
        (r.R (T (g.nodeTime i) z)-conformingWeight (ρ.multiplier w τ (g.nodeTime i)) (hw _)
          (conformingWeight (ρ.multiplier w τ (g.nodeTime i)) (hw _) (r.R z))) ≤
      ε*conformingWeightedNorm hS hν hV (w.q (g.nodeTime i)) (ρ.multiplier w τ (g.nodeTime i)) (r.R z))
    (hsmall : Cf*ε+ηA*(ε+CM) ≤ c/2)
    (f : g.Sequence (Lp ℝ 2 ν)) (u : g.Sequence V) (z : g.Sequence X)
    (hu : ∀ (i : g.Index) (v : V), inner ℝ (s.difference g (fun k => (u k : Lp ℝ 2 ν)) i) (v : Lp ℝ 2 ν)+
      Reconstruction.spatialForm a (μ i) (u i) v = inner ℝ (f i) (v : Lp ℝ 2 ν))
    (hz : ∀ i, s.difference g z i+A (z i)+μ i • r.G (z i) = r.J (f i)) :
    g.weightedNorm (energySeminorm hS hν hV g ρ w τ) (fun i => r.R (z i-r.J (u i : Lp ℝ 2 ν))) ≤
      (2/c)*(ε+CM)*(Cf*g.weightedNorm (energySeminorm hS hν hV g ρ w τ)
        (fun i => u i-r.Q (u i : Lp ℝ 2 ν))+
        ηA*g.weightedNorm (energySeminorm hS hν hV g ρ w τ) (fun i => r.Q (u i : Lp ℝ 2 ν))) := by
  let p := energySeminorm hS hν hV g ρ w τ
  let q := energySeminorm hS hν hV g ρ.neg w (-τ)
  let M : g.Index → V →ₗ[ℝ] V := fun i =>
    (conformingWeight (ρ.multiplier w τ (g.nodeTime i)) (hw _)).comp
      (conformingWeight (ρ.multiplier w τ (g.nodeTime i)) (hw _))
  let e : g.Sequence X := fun i => z i-r.J (u i : Lp ℝ 2 ν)
  have hp (i : g.Index) (v : V) : p i v = conformingWeightedNorm hS hν hV (w.q (g.nodeTime i))
      (ρ.multiplier w τ (g.nodeTime i)) v := conformingWeightedSeminorm_apply _ _ _ (w.nonneg _) _ _
  have hq (i : g.Index) (v : V) : q i v = conformingWeightedNorm hS hν hV (w.q (g.nodeTime i))
      (ρ.neg.multiplier w (-τ) (g.nodeTime i)) v := conformingWeightedSeminorm_apply _ _ _ (w.nonneg _) _ _
  have hs' : ∀ i x, q i (r.R (T (g.nodeTime i) x)-M i (r.R x)) ≤ ε*p i (r.R x) := by
    intro i x
    simpa only [hp,hq,M,LinearMap.comp_apply] using hsuper i x
  have htest : ∀ i x, q i (r.R (T (g.nodeTime i) x)) ≤ (ε+CM)*p i (r.R x) := by
    intro i x
    exact r.spatial_test_stability (p i) (q i) (T (g.nodeTime i)) (M i) (hs' i)
      (fun v => by simpa only [hp,hq,M,LinearMap.comp_apply] using hmul i v) x
  have ht : -(18*Ctime)*(g.dt*∑ i, (w.q (g.nodeTime i)*
      (ρ.multiplier w τ (g.nodeTime i)).seminorm (r.RH (e i)))^2) ≤
      g.pairing (s.difference g e) (fun i => T (g.nodeTime i) (e i)) := by
    cases s
    · exact ρ.pairing_test_dPlus_lower h τ τStar hτ hm hmw r.RH T T' hend hder hsym hpos hCtime htime e
    · exact ρ.pairing_test_dMinus_lower h τ τStar hτ hm hmw r.RH T T' hend hder hsym hpos hCtime htime e
  exact r.spatial_test_energy_bound g s a μ b p q (fun i => T (g.nodeTime i)) M
    hc hCf (add_nonneg hε hCM) hηA hsmall
    (fun i v z => by simpa only [hp,hq] using hform i v z)
    (fun i v z => by simpa only [hp,hq] using hdefect i v z) htest hs'
    e (fun i => r.J (u i : Lp ℝ 2 ν)) (fun i => u i-r.Q (u i : Lp ℝ 2 ν))
    (fun i => w.q (g.nodeTime i)*(ρ.multiplier w τ (g.nodeTime i)).seminorm (r.RH (e i)))
    (fun i => by simpa only [hp,M,LinearMap.comp_apply,Reconstruction.RH_apply] using hcoer i (r.R (e i))) ht
    (fun i => r.spatial_error_equation g s a A b hA μ f u z hu hz i (T (g.nodeTime i) (e i)))

end Section4
end Carleman
