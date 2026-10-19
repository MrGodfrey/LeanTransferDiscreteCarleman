module

public import Carleman.Spatial.WeakH2EvenLocalSmoothing
public import Carleman.Spatial.WeakJetLocality
public import Carleman.Spatial.WeakH2LocalContinuous

/-! Actual local L2 limits restrict to the original domain and its genuine weak fields. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d m : ℕ} {S T K : Set (SpatialCoordinates d)}

theorem local_L2_error_restrict_tendsto (hK : IsCompact K) (hTK : T ⊆ K) (hKS : K ⊆ S)
    (w : Lp ℝ 2 (volume.restrict S)) (z : Lp ℝ 2 (volume.restrict T))
    (hz : w =ᵐ[volume.restrict T] z) (F : ℕ → SpatialCoordinates d → ℝ)
    (hF : ∀ n, Continuous (F n))
    (ht : Tendsto (fun n => bochnerL2Norm (volume.restrict K) (fun x => F n x-w x)) atTop (𝓝 0)) :
    Tendsto (fun n => bochnerL2Norm (volume.restrict T) (fun x => F n x-z x)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) _ ht
  intro n
  have he : (fun x => F n x-z x) =ᵐ[volume.restrict T] (fun x => F n x-w x) := by
    filter_upwards [hz] with x hx; rw [hx]
  rw [bochnerL2Norm_congr_ae he]
  exact bochnerL2Norm_mono_measure
    ((continuous_memLp_compact hK (hF n)).sub
      ((Lp.memLp w).mono_measure (Measure.restrict_mono hKS le_rfl)))
    (Measure.restrict_mono hTK le_rfl)

theorem WeakSobolevJet.restrictSubdomain_component_ae (hTS : T ⊆ S)
    (u : WeakSobolevJet d m (volume.restrict S) S)
    (v : WeakSobolevJet d m (volume.restrict T) T)
    (he : restrictSubdomain hTS u=v) (k : Fin (m+1)) (α : Sym (Fin d) k.val) :
    derivativeComponent α (field k u) =ᵐ[volume.restrict T] derivativeComponent α (field k v) := by
  rw [← he]
  change derivativeComponent α (field k u) =ᵐ[volume.restrict T]
    derivativeComponent α (subdomainLp hTS (field k u))
  rw [derivativeComponent_subdomain]
  exact (subdomainLp_ae hTS _).symm

end Carleman
