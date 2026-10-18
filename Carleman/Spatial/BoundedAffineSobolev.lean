module

public import Carleman.Spatial.AffineWeakGradient
public import Carleman.Spatial.RealL2Integral

/-! Actual affine polynomials and their constant weak derivatives on a
bounded domain, as genuine L² equivalence classes. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem scalarLp_norm_sq {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (u : Lp ℝ 2 ν) :
    ‖u‖^2=∫ x, (u x)^2 ∂ν := by
  have he := integral_sq_eq_bochnerL2Norm_sq (Lp.memLp u)
  rw [bochnerL2Norm_eq _ (Lp.memLp u),Lp.toLp_coeFn] at he
  exact he.symm

def scalarConstantLp {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (c : ℝ) : Lp ℝ 2 ν := (memLp_const c).toLp (fun _ => c)

theorem scalarConstantLp_ae {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (c : ℝ) : scalarConstantLp ν c =ᵐ[ν] (fun _ => c) := MemLp.coeFn_toLp _

theorem norm_sub_scalarConstantLp_sq {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (u : Lp ℝ 2 ν) (c : ℝ) :
    ‖u-scalarConstantLp ν c‖^2 = ∫ x, (u x-c)^2 ∂ν := by
  have he := integral_sq_eq_bochnerL2Norm_sq (Lp.memLp (u-scalarConstantLp ν c))
  rw [bochnerL2Norm_eq _ (Lp.memLp (u-scalarConstantLp ν c)),Lp.toLp_coeFn] at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u (scalarConstantLp ν c),scalarConstantLp_ae ν c] with x hx hc
  rw [hx,Pi.sub_apply,hc]

variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem boundedAffine_memLp (hb : Bornology.IsBounded S) (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    MemLp p 2 (volume.restrict S) := by
  apply (memLp_two_iff_integrable_sq p.continuous_of_finiteDimensional.aestronglyMeasurable).mpr
  exact ((p.continuous_of_finiteDimensional.pow 2).continuousOn.integrableOn_compact
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)).mono_set subset_closure

def boundedAffineLp (hb : Bornology.IsBounded S) (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    Lp ℝ 2 (volume.restrict S) := (boundedAffine_memLp hb p).toLp p

theorem boundedAffineLp_ae (hb : Bornology.IsBounded S) (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    boundedAffineLp hb p =ᵐ[volume.restrict S] p := MemLp.coeFn_toLp _

theorem boundedAffineLp_weak [IsFiniteMeasure (volume.restrict S)]
    (hb : Bornology.IsBounded S) (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (e : SpatialCoordinates d) :
    IsWeakSpatialDerivative (volume.restrict S) S e (boundedAffineLp hb p)
      (scalarConstantLp (volume.restrict S) (affineScalarDerivative p e)) := by
  apply weakSpatialDerivative_of_lipschitz (affineScalar_lipschitz p) e _ _ (boundedAffineLp_ae hb p)
  filter_upwards [scalarConstantLp_ae (volume.restrict S) (affineScalarDerivative p e)] with x hx
  rw [hx,((affineScalar_hasFDerivAt p x).hasLineDerivAt e).lineDeriv]

theorem IsWeakSpatialDerivative.sub {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    {e : SpatialCoordinates d} {u v u' v' : Lp ℝ 2 ν}
    (h : IsWeakSpatialDerivative ν S e u v) (h' : IsWeakSpatialDerivative ν S e u' v') :
    IsWeakSpatialDerivative ν S e (u-u') (v-v') := by
  simpa only [neg_one_smul,sub_eq_add_neg] using h.add (h'.smul (-1))

end Carleman
