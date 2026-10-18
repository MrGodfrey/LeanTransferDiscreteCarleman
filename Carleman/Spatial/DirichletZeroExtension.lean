module

public import Carleman.Spatial.DirichletTestPairing

/-! Zero extension preserves the genuine H¹ jet for H¹₀ states. The global
weak identity follows from the defining closure of all compact smooth tests. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem dirichlet_zeroExtend_weak_derivative (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (i : Fin d) :
    IsWeakSpatialDerivative volume univ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u))
      (zeroExtendLp hS.measurableSet
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))) := by
  apply IsWeakSpatialDerivative.iff_integral.mpr
  intro φ
  rw [integral_mul_zeroExtendLp,integral_mul_zeroExtendLp]
  have hh := dirichlet_full_test_pairing hS u hu i φ
  rw [L2.inner_def,L2.inner_def] at hh
  have hl : (∫ x in S, fderiv ℝ φ.value x (EuclideanSpace.basisFun (Fin d) ℝ i) *
      WeakSobolevJet.value u x) =
      ∫ x in S, inner ℝ (WeakSobolevJet.value u x)
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i) x) := by
    apply integral_congr_ae
    filter_upwards [φ.derivativeLp_ae (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)] with x hx
    simp only [hx,RCLike.inner_apply,conj_trivial]
  have hr : (∫ x in S, φ.value x *
      derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) x) =
      ∫ x in S, inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) x)
        (φ.toLp (volume.restrict S) x) := by
    apply integral_congr_ae
    filter_upwards [φ.toLp_ae (volume.restrict S)] with x hx
    simp only [hx,RCLike.inner_apply,conj_trivial]
  rw [hl,hr]
  exact hh

theorem derivativeComponent_zeroExtend (hS : MeasurableSet S) {k : ℕ}
    (α : Sym (Fin d) k) (u : Lp (DerivativeFiber d k) 2 (volume.restrict S)) :
    derivativeComponent α (zeroExtendLp hS u) = zeroExtendLp hS (derivativeComponent α u) := by
  apply Lp.ext
  have hu := (ae_restrict_iff' hS).mp (derivativeComponent_ae α u)
  filter_upwards [derivativeComponent_ae α (zeroExtendLp hS u),zeroExtendLp_ae hS u,
    zeroExtendLp_ae hS (derivativeComponent α u),hu] with x h1 h2 h3 h4
  rw [h1,h2,h3]
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx,h4 hx]
  · simp only [indicator_of_notMem hx,PiLp.zero_apply]

def WeakSobolevJet.zeroExtendDirichlet (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S) :
    WeakSobolevJet d 1 volume univ := by
  refine ⟨fun k => zeroExtendLp hS.measurableSet (u.val k),?_⟩
  intro k α i
  have hk : k = 0 := Fin.eq_zero k
  subst k
  have ha : α = Sym.nil := Sym.eq_nil_of_card_zero α
  subst α
  change IsWeakSpatialDerivative volume univ _
    (derivativeComponent Sym.nil (zeroExtendLp hS.measurableSet (WeakSobolevJet.field 0 u)))
    (derivativeComponent (Sym.cons i Sym.nil) (zeroExtendLp hS.measurableSet (WeakSobolevJet.field 1 u)))
  rw [derivativeComponent_zeroExtend,derivativeComponent_zeroExtend]
  exact dirichlet_zeroExtend_weak_derivative hS u hu i

theorem WeakSobolevJet.zeroExtendDirichlet_value (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S) :
    value (zeroExtendDirichlet hS u hu) = zeroExtendLp hS.measurableSet (value u) :=
  derivativeComponent_zeroExtend hS.measurableSet Sym.nil _

theorem WeakSobolevJet.zeroExtendDirichlet_field_norm (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (k : Fin 2) : ‖field k (zeroExtendDirichlet hS u hu)‖ = ‖field k u‖ :=
  zeroExtendLp_norm hS.measurableSet _

theorem WeakSobolevJet.zeroExtendDirichlet_restrict (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S) :
    restrictDomain S (zeroExtendDirichlet hS u hu) = u := by
  apply Subtype.ext
  funext k
  apply Lp.ext
  exact (Physical.restrictRegionLp_ae S _).trans (zeroExtendLp_ae_restrict hS.measurableSet _)

end Carleman
