module

public import Carleman.Spatial.DirichletPoincare
public import Carleman.Spatial.SobolevRestriction
public import Carleman.Spatial.ZeroExtensionLp

/-! H¹₀ admits integration by parts against full-space tests, via its actual closure. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem SpatialTest.dirichlet_full_test_pairing (ψ : SpatialTest S)
    (φ : SpatialTest (univ : Set (SpatialCoordinates d))) (e : SpatialCoordinates d) :
    inner ℝ (ψ.toLp (volume.restrict S)) (φ.derivativeLp (volume.restrict S) e) =
      -inner ℝ (ψ.derivativeLp (volume.restrict S) e) (φ.toLp (volume.restrict S)) := by
  obtain ⟨C,hψ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport ψ.compact ψ.smooth (by simp)
  obtain ⟨D,hφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.compact φ.smooth (by simp)
  have hi := hψ.integral_lineDeriv_mul_eq (μ := volume) hφ φ.compact e
  have hdψ (x : SpatialCoordinates d) : lineDeriv ℝ ψ.value x e = fderiv ℝ ψ.value x e :=
    ((ψ.smooth.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv
  have hdφ (x : SpatialCoordinates d) : lineDeriv ℝ φ.value x (-e) = -fderiv ℝ φ.value x e := by
    rw [((φ.smooth.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv,map_neg]
  simp_rw [hdψ,hdφ,neg_mul] at hi
  rw [integral_neg] at hi
  have hl : inner ℝ (ψ.toLp (volume.restrict S)) (φ.derivativeLp (volume.restrict S) e) =
      ∫ x, fderiv ℝ φ.value x e*ψ.value x := by
    rw [L2.inner_def]
    calc
      _ = ∫ x in S, fderiv ℝ φ.value x e*ψ.value x := by
        apply integral_congr_ae
        filter_upwards [ψ.toLp_ae (volume.restrict S),φ.derivativeLp_ae (volume.restrict S) e]
          with x hx hy
        simp only [hx,hy,RCLike.inner_apply,conj_trivial]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (ψ.support hh)),mul_zero])
  have hr : inner ℝ (ψ.derivativeLp (volume.restrict S) e) (φ.toLp (volume.restrict S)) =
      ∫ x, fderiv ℝ ψ.value x e*φ.value x := by
    rw [L2.inner_def]
    calc
      _ = ∫ x in S, fderiv ℝ ψ.value x e*φ.value x := by
        apply integral_congr_ae
        filter_upwards [ψ.derivativeLp_ae (volume.restrict S) e,φ.toLp_ae (volume.restrict S)]
          with x hx hy
        simp only [hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (ψ.support hh)),zero_apply,zero_mul])
  rw [hl,hr]
  linarith

theorem dirichlet_full_test_pairing (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (i : Fin d) (φ : SpatialTest (univ : Set (SpatialCoordinates d))) :
    inner ℝ (WeakSobolevJet.value u)
      (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)) =
      -inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
        (φ.toLp (volume.restrict S)) := by
  have hc : IsClosed {v : WeakSobolevJet d 1 (volume.restrict S) S |
      inner ℝ (WeakSobolevJet.value v)
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)) =
      -inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 v))
        (φ.toLp (volume.restrict S))} :=
    isClosed_eq (WeakSobolevJet.valueCLM.continuous.inner continuous_const)
      ((((derivativeComponentCLM (Sym.cons i Sym.nil)).continuous.comp
        (WeakSobolevJet.fieldCLM 1).continuous).inner continuous_const).neg)
  apply closure_minimal (s := (Submodule.span ℝ (Set.range (fun ψ : SpatialTest S => ψ.sobolevJet)) : Set _)) _ hc hu
  intro v hv
  obtain ⟨ψ,rfl⟩ := exists_test_of_mem_test_span hS hv
  change inner ℝ (WeakSobolevJet.value ψ.sobolevJet) _ = -inner ℝ
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 ψ.sobolevJet)) _
  rw [ψ.sobolevJet_value,ψ.sobolevJet_derivative]
  exact ψ.dirichlet_full_test_pairing φ _

end Carleman
