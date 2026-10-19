module

public import Carleman.Spatial.SmoothGapCutoff
public import Carleman.Spatial.WeakZeroGradientConstant
public import Carleman.Spatial.SobolevRestriction

/-! A genuine weak H¹ scalar state cannot cross a positive gap in its
essential range on a bounded open convex set. No pointwise regularity of the
original L² representative is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff NNReal
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem weak_scalar_gap_on_convex (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (v : Fin d → Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hw : ∀ i, IsWeakSpatialDerivative volume univ (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ᵐ x ∂volume.restrict S, u x=0 ∨ δ ≤ |u x|) :
    (u =ᵐ[volume.restrict S] (fun _ => 0)) ∨ (∀ᵐ x ∂volume.restrict S, δ ≤ |u x|) := by
  obtain ⟨η,M,hη,hL,h0,hd0,hout⟩ := exists_smooth_gap_cutoff hδ
  have hU : MemLp (fun x => η (u x)) 2 volume := hL.comp_memLp h0 (Lp.memLp u)
  let U := hU.toLp (fun x => η (u x))
  have hmeas : AEStronglyMeasurable (fun x => deriv η (u x)) volume :=
    (hη.continuous_deriv (by simp)).comp_aestronglyMeasurable (Lp.memLp u).aestronglyMeasurable
  have hV (i : Fin d) : MemLp (fun x => deriv η (u x)*v i x) 2 volume :=
    memLp_mul_of_ae_bound hmeas (Lp.memLp (v i)) M.property
      (Filter.Eventually.of_forall fun x => norm_deriv_le_of_lipschitz hL)
  let V := fun i => (hV i).toLp (fun x => deriv η (u x)*v i x)
  have he (i : Fin d) : Physical.restrictRegionLp S (V i)=0 := by
    apply Lp.ext
    filter_upwards [Physical.restrictRegionLp_ae S (V i),
      (hV i).coeFn_toLp.filter_mono ae_restrict_le,hgap,Lp.coeFn_zero ℝ 2 (volume.restrict S)] with x hx hy hz hzero
    rw [hx,hzero]
    change V i x=0
    rw [hy]
    rcases hz with hz | hz
    · rw [hz,hd0,zero_mul]
    · rw [(hout _ hz).2,zero_mul]
  have hlocal (i : Fin d) : IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ i) (Physical.restrictRegionLp S U) 0 := by
    have hh := ((hw i).scalar_chain_rule (hη.of_le (by simp)) hL h0 U (V i)
      hU.coeFn_toLp (hV i).coeFn_toLp).restrictDomain (S := S)
    rwa [he i] at hh
  obtain ⟨c,hcU⟩ := weak_zero_gradient_ae_constant hS hc hb (Physical.restrictRegionLp S U) hlocal
  have hcη : (fun x => η (u x)) =ᵐ[volume.restrict S] (fun _ => c) := by
    filter_upwards [hcU,Physical.restrictRegionLp_ae S U,hU.coeFn_toLp.filter_mono ae_restrict_le] with x hx hy hz
    exact hz.symm.trans (hy.symm.trans hx)
  by_cases hcz : c=0
  · left
    filter_upwards [hcη,hgap] with x hx hg
    rcases hg with hg | hg
    · exact hg
    · have hh := (hout _ hg).1
      rw [hh,hcz] at hx
      exact (one_ne_zero hx).elim
  · right
    filter_upwards [hcη,hgap] with x hx hg
    rcases hg with hg | hg
    · rw [hg,h0] at hx
      exact (hcz hx.symm).elim
    · exact hg

end Carleman
