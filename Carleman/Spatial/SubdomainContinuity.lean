module

public import Carleman.Spatial.SubdomainRestriction

/-! Restriction to a smaller spatial domain is a contraction on the genuine
L² classes and the complete weak Sobolev graph space. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d m : ℕ} {S T : Set (SpatialCoordinates d)}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem subdomainLp_norm_le (hTS : T ⊆ S) (u : Lp E 2 (volume.restrict S)) :
    ‖subdomainLp hTS u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def,Lp.norm_def,eLpNorm_congr_ae (subdomainLp_ae hTS u)]
  exact ENNReal.toReal_mono (Lp.memLp u).ne
    (eLpNorm_mono_measure u (Measure.restrict_mono hTS le_rfl))

def subdomainLinearMap (hTS : T ⊆ S) :
    Lp E 2 (volume.restrict S) →ₗ[ℝ] Lp E 2 (volume.restrict T) where
  toFun := subdomainLp hTS
  map_add' u v := by
    apply Lp.ext
    filter_upwards [subdomainLp_ae hTS (u+v),subdomainLp_ae hTS u,subdomainLp_ae hTS v,
      (Lp.coeFn_add u v).filter_mono (ae_mono (Measure.restrict_mono hTS le_rfl)),
      Lp.coeFn_add (subdomainLp hTS u) (subdomainLp hTS v)] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1,h5,h2,h3,h4]
  map_smul' c u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [subdomainLp_ae hTS (c • u),subdomainLp_ae hTS u,
      (Lp.coeFn_smul c u).filter_mono (ae_mono (Measure.restrict_mono hTS le_rfl)),
      Lp.coeFn_smul c (subdomainLp hTS u)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply] at h3 h4
    rw [h1,h4,h2,h3]

def subdomainCLM (hTS : T ⊆ S) :
    Lp E 2 (volume.restrict S) →L[ℝ] Lp E 2 (volume.restrict T) :=
  (subdomainLinearMap hTS).mkContinuous 1 (fun u => by
    change ‖subdomainLp hTS u‖ ≤ 1*‖u‖
    simpa only [one_mul] using subdomainLp_norm_le hTS u)

namespace WeakSobolevJet

theorem restrictSubdomain_norm_le (hTS : T ⊆ S)
    (u : WeakSobolevJet d m (volume.restrict S) S) : ‖restrictSubdomain hTS u‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro k
  exact (subdomainLp_norm_le hTS (u.val k)).trans (norm_field_le k u)

def restrictSubdomainLinearMap (hTS : T ⊆ S) :
    WeakSobolevJet d m (volume.restrict S) S →ₗ[ℝ] WeakSobolevJet d m (volume.restrict T) T where
  toFun := restrictSubdomain hTS
  map_add' u v := by
    apply Subtype.ext
    funext k
    exact (subdomainLinearMap hTS).map_add (u.val k) (v.val k)
  map_smul' c u := by
    apply Subtype.ext
    funext k
    exact (subdomainLinearMap hTS).map_smul c (u.val k)

def restrictSubdomainCLM (hTS : T ⊆ S) :
    WeakSobolevJet d m (volume.restrict S) S →L[ℝ] WeakSobolevJet d m (volume.restrict T) T :=
  (restrictSubdomainLinearMap hTS).mkContinuous 1 (fun u => by
    change ‖restrictSubdomain hTS u‖ ≤ 1*‖u‖
    simpa only [one_mul] using restrictSubdomain_norm_le hTS u)

theorem restrictSubdomain_test_value_ae (hTS : T ⊆ S) (φ : SpatialTest S) :
    value (restrictSubdomain hTS φ.sobolevJet) =ᵐ[volume.restrict T] φ.value := by
  rw [restrictSubdomain_value,φ.sobolevJet_value]
  exact (subdomainLp_ae hTS _).trans
    ((φ.toLp_ae (volume.restrict S)).filter_mono (ae_mono (Measure.restrict_mono hTS le_rfl)))

end WeakSobolevJet
end Carleman
