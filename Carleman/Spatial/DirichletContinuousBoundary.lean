module

public import Carleman.Spatial.WeakScalarGap
public import Carleman.Spatial.DirichletZeroExtension
public import Carleman.Spatial.WeakH2ClosureContinuous

/-! The actual continuous representative of an H¹₀ state vanishes at every
boundary point of an open convex domain. A smooth cutoff and genuine weak
Poincaré exclude a jump across the boundary, without assuming a trace theorem. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter Metric
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem dirichlet_continuous_zero_on_frontier (hS : IsOpen S) (hc : Convex ℝ S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    {f : SpatialCoordinates d → ℝ} (hf : ContinuousOn f (closure S))
    (hfu : f =ᵐ[volume.restrict S] WeakSobolevJet.value u) :
    ∀ x ∈ frontier S, f x=0 := by
  intro x hx
  by_contra hfx
  let δ := |f x|/2
  have hδ : 0 < δ := div_pos (abs_pos.mpr hfx) (by norm_num)
  obtain ⟨r,hr,hfr⟩ := Metric.continuousWithinAt_iff.mp (hf x hx.1) δ hδ
  let B := ball x r
  have hB : IsOpen B := isOpen_ball
  have hbound (y : SpatialCoordinates d) (hy : y ∈ closure S) (hyB : y ∈ B) : δ ≤ |f y| := by
    have he := hfr hy hyB
    have hn := norm_sub_norm_le (f x) (f y)
    simp only [dist_eq_norm,Real.norm_eq_abs] at he hn
    rw [abs_sub_comm] at hn
    dsimp only [δ] at hδ ⊢ he
    linarith
  let w := zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)
  let v := fun i : Fin d => zeroExtendLp hS.measurableSet
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
  have hw (i : Fin d) : IsWeakSpatialDerivative volume univ
      (EuclideanSpace.basisFun (Fin d) ℝ i) w (v i) := dirichlet_zeroExtend_weak_derivative hS u hu i
  have hrep : ∀ᵐ y ∂volume, y ∈ S → WeakSobolevJet.value u y=f y :=
    (ae_restrict_iff' hS.measurableSet).mp hfu.symm
  have hgap : ∀ᵐ y ∂volume.restrict B, w y=0 ∨ δ ≤ |w y| := by
    filter_upwards [(zeroExtendLp_ae hS.measurableSet (WeakSobolevJet.value u)).filter_mono ae_restrict_le,
      hrep.filter_mono ae_restrict_le,ae_restrict_mem hB.measurableSet] with y hy he hyB
    change w y=_ at hy
    by_cases hyS : y ∈ S
    · right
      rw [hy,indicator_of_mem hyS,he hyS]
      exact hbound y (subset_closure hyS) hyB
    · left
      rw [hy,indicator_of_notMem hyS]
  rcases weak_scalar_gap_on_convex hB (convex_ball x r) (isBounded_ball) w v hw hδ hgap with hz | hn
  · let O := S ∩ B
    have hO : IsOpen O := hS.inter hB
    have hfw : f =ᵐ[volume.restrict O] w :=
      (hfu.trans (zeroExtendLp_ae_restrict hS.measurableSet (WeakSobolevJet.value u)).symm).filter_mono
        (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))
    have hfzero : f =ᵐ[volume.restrict O] (fun _ => 0) :=
      hfw.trans (hz.filter_mono (ae_mono (Measure.restrict_mono inter_subset_right le_rfl)))
    have he := Measure.eqOn_open_of_ae_eq hfzero hO
      (hf.mono fun y hy => subset_closure hy.1) continuous_const.continuousOn
    obtain ⟨y,hyS,hyB⟩ := Metric.mem_closure_iff.mp hx.1 r hr
    have hyB' : y ∈ B := by simpa only [B,mem_ball,dist_comm] using hyB
    have hh := hbound y (subset_closure hyS) hyB'
    rw [he ⟨hyS,hyB'⟩,abs_zero] at hh
    exact (not_le_of_gt hδ) hh
  · have hreg : interior (closure S)=S := by
      by_cases hs : S.Nonempty
      · rw [hc.interior_closure_eq_interior_of_nonempty_interior (hS.interior_eq.symm ▸ hs),hS.interior_eq]
      · rw [Set.not_nonempty_iff_eq_empty.mp hs,closure_empty,interior_empty]
    have hxout : x ∈ closure (closure S)ᶜ := by
      rw [closure_compl,hreg]
      exact fun hxS => hx.2 (hS.interior_eq.symm ▸ hxS)
    let O := (closure S)ᶜ ∩ B
    have hO : IsOpen O := isClosed_closure.isOpen_compl.inter hB
    obtain ⟨y,hyout,hyB⟩ := Metric.mem_closure_iff.mp hxout r hr
    have hne : O.Nonempty := ⟨y,hyout,by simpa only [B,mem_ball,dist_comm] using hyB⟩
    have hpos : volume O ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior volume (hO.interior_eq.symm ▸ hne)).ne'
    have hbad : ∀ᵐ y ∂volume.restrict O, False := by
      filter_upwards [hn.filter_mono (ae_mono (Measure.restrict_mono inter_subset_right le_rfl)),
        (zeroExtendLp_ae hS.measurableSet (WeakSobolevJet.value u)).filter_mono ae_restrict_le,
        ae_restrict_mem hO.measurableSet] with y hy he hyO
      change w y=_ at he
      rw [he,indicator_of_notMem (fun hyS => hyO.1 (subset_closure hyS)),abs_zero] at hy
      exact (not_le_of_gt hδ) hy
    obtain ⟨_,_,hfals⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos hbad
    exact hfals

theorem WeakSobolevJet.exists_dirichlet_closure_representative
    (hS : IsOpen S) (hc : Convex ℝ S) (hb : Bornology.IsBounded S) (hd : d ≤ 3)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ dirichletSubspace S) :
    ∃ f : SpatialCoordinates d → ℝ, ContinuousOn f (closure S) ∧
      f =ᵐ[volume.restrict S] WeakSobolevJet.value u ∧ ∀ x ∈ frontier S, f x=0 := by
  obtain ⟨f,hf,he⟩ := WeakSobolevJet.exists_closure_continuous_representative hS hc hb hd u
  obtain ⟨v,hv,hvu⟩ := hu
  refine ⟨f,hf,he,?_⟩
  exact dirichlet_continuous_zero_on_frontier hS hc v hv hf (hvu.symm ▸ he)

end Carleman
