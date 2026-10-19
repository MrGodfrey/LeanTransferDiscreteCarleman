module

public import Carleman.Spatial.SimplicialLocalGradient
public import Carleman.Continuous.BochnerNormAlgebra

/-! Equality of actual values on a cell determines all weak fields there.
The argument restricts to its open interior and then restores the null boundary. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d m : ℕ} {S T : Set (SpatialCoordinates d)}

theorem WeakSobolevJet.restrictSubdomain_eq_of_value_ae (hTS : T ⊆ S) (hT : IsOpen T)
    (u : WeakSobolevJet d m (volume.restrict S) S)
    (v : WeakSobolevJet d m (volume.restrict T) T)
    (huv : value u =ᵐ[volume.restrict T] value v) : restrictSubdomain hTS u=v := by
  apply value_injective hT (ae_restrict_mem hT.measurableSet)
  apply Lp.ext
  rw [restrictSubdomain_value]
  exact (subdomainLp_ae hTS (value u)).trans huv

theorem SimplicialPartition.field_congr_on_cell {ι : Type*} (M : SimplicialPartition S ι)
    (hS : IsOpen S) (hc : Convex ℝ S) (i : ι)
    (u v : WeakSobolevJet d m (volume.restrict S) S)
    (huv : WeakSobolevJet.value u =ᵐ[volume.restrict (M.cell i)] WeakSobolevJet.value v)
    (k : Fin (m+1)) :
    WeakSobolevJet.field k u =ᵐ[volume.restrict (M.cell i)] WeakSobolevJet.field k v := by
  let hIS := M.cell_interior_subset hS hc i
  have hh : WeakSobolevJet.restrictSubdomain hIS u=WeakSobolevJet.restrictSubdomain hIS v := by
    apply WeakSobolevJet.restrictSubdomain_eq_of_value_ae hIS isOpen_interior
    rw [WeakSobolevJet.restrictSubdomain_value]
    exact (huv.filter_mono (ae_mono (Measure.restrict_mono interior_subset le_rfl))).trans
      (subdomainLp_ae hIS (WeakSobolevJet.value v)).symm
  have hk : subdomainLp hIS (WeakSobolevJet.field k u)=subdomainLp hIS (WeakSobolevJet.field k v) :=
    congrArg (WeakSobolevJet.field k) hh
  have he := (subdomainLp_ae hIS (WeakSobolevJet.field k u)).symm.trans
    (hk ▸ subdomainLp_ae hIS (WeakSobolevJet.field k v))
  rwa [← Measure.restrict_congr_set (simplexCell_ae_interior (M.simplex i))] at he

theorem bochnerL2Norm_mono_measure {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ ν : Measure X} {f : X → E} (hf : MemLp f 2 μ) (hνμ : ν ≤ μ) :
    bochnerL2Norm ν f ≤ bochnerL2Norm μ f :=
  ENNReal.toReal_mono hf.ne (eLpNorm_mono_measure f hνμ)

theorem bochnerL2Norm_lp_sub {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ ν : Measure X} (hνμ : ν ≤ μ) (u v : Lp E 2 μ) :
    bochnerL2Norm ν (u-v) ≤ bochnerL2Norm ν u+bochnerL2Norm ν v := by
  rw [bochnerL2Norm_congr_ae ((Lp.coeFn_sub u v).filter_mono (ae_mono hνμ))]
  exact bochnerL2Norm_sub ((Lp.memLp u).mono_measure hνμ) ((Lp.memLp v).mono_measure hνμ)

end Carleman
