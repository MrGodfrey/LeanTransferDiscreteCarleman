module

public import Carleman.Spatial.DirichletExtensionPairing
public import Carleman.Spatial.SpatialTestDerivative

/-! The Hessian of an inner-domain solution is extended componentwise.
Its integration-by-parts identity holds for tests supported inside that
domain, without asserting that the global zero extension is H². -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

theorem subdomainZeroExtend_test_inner (hT : MeasurableSet T) (hTS : T ⊆ S)
    (u : Lp ℝ 2 (volume.restrict T)) (φ : SpatialTest T) :
    inner ℝ (subdomainZeroExtend S hT u) ((φ.monoDomain hTS).toLp (volume.restrict S)) =
      inner ℝ u (φ.toLp (volume.restrict T)) := by
  rw [subdomainZeroExtend_inner hT hTS]
  congr 1
  apply Lp.ext
  exact (subdomainLp_ae hTS _).trans
    (((φ.monoDomain hTS).toLp_ae (volume.restrict S)).filter_mono
      (ae_mono (Measure.restrict_mono hTS le_rfl)) |>.trans (φ.toLp_ae (volume.restrict T)).symm)

theorem subdomainZeroExtend_derivativeTest_inner (hT : MeasurableSet T) (hTS : T ⊆ S)
    (u : Lp ℝ 2 (volume.restrict T)) (φ : SpatialTest T) (e : SpatialCoordinates d) :
    inner ℝ (subdomainZeroExtend S hT u) ((φ.monoDomain hTS).derivativeLp (volume.restrict S) e) =
      inner ℝ u (φ.derivativeLp (volume.restrict T) e) := by
  have he := subdomainZeroExtend_test_inner hT hTS u (φ.derivativeTest e)
  change inner ℝ (subdomainZeroExtend S hT u)
    (((φ.monoDomain hTS).derivativeTest e).toLp (volume.restrict S)) = _ at he
  simpa only [SpatialTest.derivativeTest_toLp] using he

theorem derivativeComponent_subdomainZeroExtend {k : ℕ} (hT : MeasurableSet T)
    (α : Sym (Fin d) k) (u : Lp (DerivativeFiber d k) 2 (volume.restrict T)) :
    derivativeComponent α (subdomainZeroExtend S hT u) =
      subdomainZeroExtend S hT (derivativeComponent α u) := by
  unfold subdomainZeroExtend
  rw [derivativeComponent_restrict,derivativeComponent_zeroExtend]

theorem WeakSobolevJet.extendDirichlet_hessian_test (hT : IsOpen T) (hTS : T ⊆ S)
    (u : WeakSobolevJet d 2 (volume.restrict T) T)
    (hu : truncate (by decide : 1 ≤ 2) u ∈ dirichletJetSpace T)
    (i j : Fin d) (φ : SpatialTest T) :
    inner ℝ (derivativeComponent (Sym.cons i Sym.nil)
      (field 1 (extendDirichlet S hT (truncate (by decide : 1 ≤ 2) u) hu)))
      ((φ.monoDomain hTS).derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)) =
      -inner ℝ (subdomainZeroExtend S hT.measurableSet
        (derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (field 2 u)))
        ((φ.monoDomain hTS).toLp (volume.restrict S)) := by
  rw [extendDirichlet_field,derivativeComponent_subdomainZeroExtend,
    subdomainZeroExtend_derivativeTest_inner hT.measurableSet hTS,
    subdomainZeroExtend_test_inner hT.measurableSet hTS]
  exact u.property 1 (Sym.cons i Sym.nil) j φ

end Carleman
