module

public import Carleman.Spatial.AllowedCartesianKuhnError
public import Carleman.Spatial.CartesianReconstructionInterface
public import Carleman.Spatial.LaplacianCorrectionBounds
public import Carleman.Section4.ApproximationData

/-! The original full H² Cartesian estimate supplies the actual N3 interface,
with a_E = C h and a_0 = C h² on every H² Dirichlet domain subspace. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman

theorem cartesian_heat_error_from_b2 {d : ℕ} {S : Set (SpatialCoordinates d)}
    {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    (e : WeakSobolevJet d 1 ν S) (u : WeakSobolevJet d 2 ν S)
    (σ : BoundedMultiplier ν) (q h C : ℝ) (hq : 0 ≤ q) (hh : 0 < h) (hC : 0 ≤ C)
    (hsmall : h*q ≤ 1)
    (hb : σ.seminorm (WeakSobolevJet.value e)+h*σ.seminorm (WeakSobolevJet.field 1 e) ≤
      C*h^2*σ.seminorm (WeakSobolevJet.field 2 u)) :
    WeakSobolevJet.weightedNorm q σ e ≤ (C*h)*WeakSobolevJet.parameterNorm q σ u ∧
      σ.seminorm (WeakSobolevJet.value e) ≤ (C*h^2)*WeakSobolevJet.parameterNorm q σ u := by
  have htop : σ.seminorm (WeakSobolevJet.field 2 u) ≤ WeakSobolevJet.parameterNorm q σ u := by
    have ht := WeakSobolevJet.parameterNorm_component hq σ u 2
    change q^0*σ.seminorm (WeakSobolevJet.field 2 u) ≤ _ at ht
    simpa only [pow_zero,one_mul] using ht
  have hb' := hb.trans (mul_le_mul_of_nonneg_left htop (by positivity : 0 ≤ C*h^2))
  have henergy := WeakSobolevJet.weightedNorm_le_parameterNorm hq σ e
  have hheat : WeakSobolevJet.parameterNorm q σ e=
      q*σ.seminorm (WeakSobolevJet.value e)+σ.seminorm (WeakSobolevJet.field 1 e) := by
    unfold WeakSobolevJet.parameterNorm
    rw [Fin.sum_univ_two]
    norm_num only [Fin.val_zero,Fin.val_one,Nat.sub_zero,Nat.sub_self,pow_one,pow_zero,one_mul]
    rw [WeakSobolevJet.weighted_zero_eq]
  rw [hheat] at henergy
  constructor
  · apply le_of_mul_le_mul_left (a := h)
    · calc
        h*WeakSobolevJet.weightedNorm q σ e ≤
            h*(q*σ.seminorm (WeakSobolevJet.value e)+σ.seminorm (WeakSobolevJet.field 1 e)) :=
          mul_le_mul_of_nonneg_left henergy hh.le
        _ ≤ σ.seminorm (WeakSobolevJet.value e)+h*σ.seminorm (WeakSobolevJet.field 1 e) := by
          have hp := mul_le_mul_of_nonneg_right hsmall (apply_nonneg σ.seminorm (WeakSobolevJet.value e))
          nlinarith only [hp]
        _ ≤ C*h^2*WeakSobolevJet.parameterNorm q σ u := hb'
        _ = _ := by ring
    · exact hh
  · exact (le_add_of_nonneg_right (mul_nonneg hh.le (apply_nonneg _ _))).trans hb'

theorem cartesian_weightedApproximation_interface {d : ℕ} {S : Set (SpatialCoordinates (d+1))}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > (0:ℝ), ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
      (hdom : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=S) (h : ℝ),
      0 < h → (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
    ∀ (D : Submodule ℝ (Lp ℝ 2 (volume.restrict S)))
      (hD : D ≤ sobolevSubspace (d+1) (2*1) (volume.restrict S) S)
      (hDV : D ≤ dirichletSubspace S) (w : TimeWeight) (g : TimeGrid) (τ η : ℝ),
      |η|=1 → h*w.max ≤ 1 →
      Section4.WeightedApproximation hS (ae_restrict_mem hS.measurableSet)
        (dirichletSubspace_sobolev S) hD hDV (hdom ▸ cartesianReconstruction o δ hδ N)
        g (ρ.scaled η) w τ (C*h) (C*h^2) := by
  obtain ⟨C,hC,hbound⟩ := allowed_weight_cartesianKuhn_h2_error hS hc hcompact ρ hρ κ hκ
  refine ⟨C,hC,?_⟩
  intro o δ hδ N hdom h hh hlower hupper D hD hDV w g τ η hη hsmall
  subst S
  let hν := ae_restrict_mem (μ := volume) hS.measurableSet
  let hV := dirichletSubspace_sobolev (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
  let r := cartesianReconstruction o δ hδ N
  have hpoint (t : ℝ) (v : D) :
      conformingWeightedNorm hS hν hV (w.q t) ((ρ.scaled η).multiplier w τ t)
        (Submodule.inclusion hDV v-r.Q (v : Lp ℝ 2 _)) ≤
        (C*h)*conformingParameterNorm hS hν hD (w.q t) ((ρ.scaled η).multiplier w τ t) v ∧
      ((ρ.scaled η).multiplier w τ t).seminorm
        ((v : Lp ℝ 2 _)-r.RH (r.J (v : Lp ℝ 2 _))) ≤
        (C*h^2)*conformingParameterNorm hS hν hD (w.q t) ((ρ.scaled η).multiplier w τ t) v := by
    let u := domainSobolevJet hS hν hD v
    let e := cartesianKuhnErrorJet o δ hδ N (WeakSobolevJet.truncate (by omega : 1 ≤ 2) u)
    let σ := (ρ.scaled η).multiplier w τ t
    have hqt : h*w.q t ≤ 1 := (mul_le_mul_of_nonneg_left (w.upper t) hh.le).trans hsmall
    have hu : WeakSobolevJet.value u ∈ dirichletSubspace _ := by
      rw [domainSobolevJet_value]
      exact hDV v.property
    have hb := hbound o δ hδ N (Subset.refl _) h hh hlower hupper w τ t η hη hqt u hu
    have he : e=domainSobolevJet hS hν hV
        (Submodule.inclusion hDV v-r.Q (v : Lp ℝ 2 _)) := by
      apply WeakSobolevJet.value_injective hS hν
      rw [domainSobolevJet_value]
      change WeakSobolevJet.value e=(v : Lp ℝ 2 _)-r.QH (v : Lp ℝ 2 _)
      rw [cartesianReconstruction_QH]
      dsimp only [e,cartesianKuhnErrorJet]
      rw [map_sub,WeakSobolevJet.truncate_value,cartesianKuhnProjectionJet_value,
        domainSobolevJet_value]
    have hn := cartesian_heat_error_from_b2 e u σ (w.q t) h C (w.nonneg t) hh hC.le hqt hb
    rw [he,domainSobolevJet_value] at hn
    exact hn
  exact ⟨fun t _ v => (hpoint t v).1,fun t _ v => (hpoint t v).2⟩

end Carleman
