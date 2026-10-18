module

public import Carleman.Spatial.DirichletSpace
public import Carleman.Control.ObservedRegionLp

/-! Restriction of genuine full-space weak Sobolev jets to an open domain,
with actual L² fields and continuity in the full graph topology. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
set_option maxHeartbeats 1200000
namespace Carleman
open Physical
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}

def SpatialTest.toUniv (φ : SpatialTest S) : SpatialTest (univ : Set (SpatialCoordinates d)) where
  value := φ.value
  smooth := φ.smooth
  compact := φ.compact
  support := subset_univ _

theorem IsWeakSpatialDerivative.restrictDomain {e : SpatialCoordinates d}
    {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (h : IsWeakSpatialDerivative volume univ e u v) :
    IsWeakSpatialDerivative (volume.restrict S) S e (restrictRegionLp S u) (restrictRegionLp S v) := by
  rw [IsWeakSpatialDerivative.iff_integral]
  intro φ
  have hi := IsWeakSpatialDerivative.iff_integral.mp h φ.toUniv
  have hu : (∫ x in S, fderiv ℝ φ.value x e * restrictRegionLp S u x) =
      ∫ x, fderiv ℝ φ.value x e * u x := by
    calc
      _ = ∫ x in S, fderiv ℝ φ.value x e * u x := by
        apply integral_congr_ae
        filter_upwards [restrictRegionLp_ae S u] with x hx
        rw [hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (φ.support hh)),zero_apply,zero_mul])
  have hv : (∫ x in S, φ.value x * restrictRegionLp S v x) = ∫ x, φ.value x * v x := by
    calc
      _ = ∫ x in S, φ.value x * v x := by
        apply integral_congr_ae
        filter_upwards [restrictRegionLp_ae S v] with x hx
        rw [hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (φ.support hh)),zero_mul])
  rw [hu,hv]
  exact hi

theorem derivativeComponent_restrict {k : ℕ} (α : Sym (Fin d) k)
    (u : Lp (DerivativeFiber d k) 2 (volume : Measure (SpatialCoordinates d))) :
    derivativeComponent α (restrictRegionLp S u) = restrictRegionLp S (derivativeComponent α u) := by
  apply Lp.ext
  filter_upwards [derivativeComponent_ae α (restrictRegionLp S u),restrictRegionLp_ae S u,
    restrictRegionLp_ae S (derivativeComponent α u),
    (derivativeComponent_ae α u).filter_mono ae_restrict_le] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

def WeakSobolevJet.restrictDomain (S : Set (SpatialCoordinates d))
    (u : WeakSobolevJet d m volume univ) : WeakSobolevJet d m (volume.restrict S) S := by
  refine ⟨fun k => restrictRegionLp S (u.val k),?_⟩
  intro k α i
  change IsWeakSpatialDerivative (volume.restrict S) S _
    (derivativeComponent α (restrictRegionLp S (u.val k.castSucc)))
    (derivativeComponent (Sym.cons i α) (restrictRegionLp S (u.val k.succ)))
  rw [derivativeComponent_restrict,derivativeComponent_restrict]
  exact (u.property k α i).restrictDomain

theorem WeakSobolevJet.restrictDomain_value (u : WeakSobolevJet d m volume univ) :
    value (WeakSobolevJet.restrictDomain S u) = restrictRegionLp S (value u) := derivativeComponent_restrict Sym.nil _

theorem WeakSobolevJet.restrictDomain_tendsto
    {u : ℕ → WeakSobolevJet d m volume univ} {v : WeakSobolevJet d m volume univ}
    (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => WeakSobolevJet.restrictDomain S (u n)) atTop (𝓝 (WeakSobolevJet.restrictDomain S v)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro k
  exact ((restrictRegionCLM S).continuous.tendsto (v.val k)).comp
    (((WeakSobolevJet.fieldCLM k).continuous.tendsto v).comp hu)

theorem restrictedJet_eq_test (hS : IsOpen S) (φ : SpatialTest S)
    (u : WeakSobolevJet d 1 volume univ)
    (hu : WeakSobolevJet.value u =ᵐ[volume] φ.value) :
    WeakSobolevJet.restrictDomain S u = φ.sobolevJet := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [WeakSobolevJet.restrictDomain_value,φ.sobolevJet_value]
  apply Lp.ext
  exact (restrictRegionLp_ae S _).trans
    ((hu.filter_mono ae_restrict_le).trans (φ.toLp_ae (volume.restrict S)).symm)

end Carleman
