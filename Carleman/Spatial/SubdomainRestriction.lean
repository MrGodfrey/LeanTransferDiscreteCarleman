module

public import Carleman.Spatial.SobolevRestriction

/-! Genuine restriction from one spatial domain to a smaller domain.
All original tests and all derivative fields are preserved. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}
  {E : Type*} [NormedAddCommGroup E]

def subdomainLp (hTS : T ⊆ S) (u : Lp E 2 (volume.restrict S)) :
    Lp E 2 (volume.restrict T) :=
  ((Lp.memLp u).mono_measure (Measure.restrict_mono hTS le_rfl)).toLp u

theorem subdomainLp_ae (hTS : T ⊆ S) (u : Lp E 2 (volume.restrict S)) :
    subdomainLp hTS u =ᵐ[volume.restrict T] u := MemLp.coeFn_toLp _

def SpatialTest.monoDomain (hTS : T ⊆ S) (φ : SpatialTest T) : SpatialTest S where
  value := φ.value
  smooth := φ.smooth
  compact := φ.compact
  support := φ.support.trans hTS

theorem IsWeakSpatialDerivative.restrictSubdomain (hTS : T ⊆ S) {e : SpatialCoordinates d}
    {u v : Lp ℝ 2 (volume.restrict S)}
    (h : IsWeakSpatialDerivative (volume.restrict S) S e u v) :
    IsWeakSpatialDerivative (volume.restrict T) T e (subdomainLp hTS u) (subdomainLp hTS v) := by
  rw [IsWeakSpatialDerivative.iff_integral]
  intro φ
  have hi := IsWeakSpatialDerivative.iff_integral.mp h (φ.monoDomain hTS)
  have eqInt (g : SpatialCoordinates d → ℝ) (hg : ∀ x ∉ T, g x=0) :
      (∫ x in T, g x) = ∫ x in S, g x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hg,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hg x (fun ht => hx (hTS ht)))]
  have hu : (∫ x in T, fderiv ℝ φ.value x e*subdomainLp hTS u x) =
      ∫ x in S, fderiv ℝ φ.value x e*u x := by
    calc
      _ = ∫ x in T, fderiv ℝ φ.value x e*u x := by
        apply integral_congr_ae
        filter_upwards [subdomainLp_ae hTS u] with x hx
        rw [hx]
      _ = _ := eqInt _ (fun x hx => by
        rw [fderiv_of_notMem_tsupport ℝ (fun ht => hx (φ.support ht)),zero_apply,zero_mul])
  have hv : (∫ x in T, φ.value x*subdomainLp hTS v x) = ∫ x in S, φ.value x*v x := by
    calc
      _ = ∫ x in T, φ.value x*v x := by
        apply integral_congr_ae
        filter_upwards [subdomainLp_ae hTS v] with x hx
        rw [hx]
      _ = _ := eqInt _ (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.support ht)),zero_mul])
  rw [hu,hv]
  exact hi

theorem derivativeComponent_subdomain {k : ℕ} (hTS : T ⊆ S) (α : Sym (Fin d) k)
    (u : Lp (DerivativeFiber d k) 2 (volume.restrict S)) :
    derivativeComponent α (subdomainLp hTS u) = subdomainLp hTS (derivativeComponent α u) := by
  apply Lp.ext
  filter_upwards [derivativeComponent_ae α (subdomainLp hTS u),subdomainLp_ae hTS u,
    subdomainLp_ae hTS (derivativeComponent α u),
    (derivativeComponent_ae α u).filter_mono (ae_mono (Measure.restrict_mono hTS le_rfl))]
    with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

def WeakSobolevJet.restrictSubdomain {m : ℕ} (hTS : T ⊆ S)
    (u : WeakSobolevJet d m (volume.restrict S) S) : WeakSobolevJet d m (volume.restrict T) T := by
  refine ⟨fun k => subdomainLp hTS (u.val k),?_⟩
  intro k α i
  change IsWeakSpatialDerivative (volume.restrict T) T _
    (derivativeComponent α (subdomainLp hTS (u.val k.castSucc)))
    (derivativeComponent (Sym.cons i α) (subdomainLp hTS (u.val k.succ)))
  rw [derivativeComponent_subdomain,derivativeComponent_subdomain]
  exact (u.property k α i).restrictSubdomain hTS

theorem WeakSobolevJet.restrictSubdomain_value {m : ℕ} (hTS : T ⊆ S)
    (u : WeakSobolevJet d m (volume.restrict S) S) :
    value (WeakSobolevJet.restrictSubdomain hTS u) = subdomainLp hTS (value u) :=
  derivativeComponent_subdomain hTS Sym.nil _

end Carleman
