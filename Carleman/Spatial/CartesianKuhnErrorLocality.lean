module

public import Carleman.Spatial.CartesianKuhnWeakInverse
public import Carleman.Spatial.CartesianKuhnLocalAffine
public import Carleman.Spatial.WeakJetLocality

/-! The actual error jet and its invariance under locally reproduced affine
functions. All fields are the original distributional weak derivatives. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianClippedPatch_cell_measure (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N) :
    volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points) ≤
      volume.restrict (cartesianClippedPatch o δ N i) := by
  rw [Measure.restrict_congr_set (simplexCell_ae_interior (cartesianFiniteSimplex o δ hδ N i))]
  apply Measure.restrict_mono _ le_rfl
  intro x hx
  exact cartesianClippedPatch_contains_cell o δ hδ N i ⟨interior_subset hx,
    (cartesianKuhnPartition o δ hδ N).cell_interior_subset
      (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) i hx⟩

theorem cartesianKuhnProjectionJet_ae (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    WeakSobolevJet.value (cartesianKuhnProjectionJet o δ hδ N u) =ᵐ[volume.restrict
      (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))] cartesianKuhnProjection o δ hδ N u := by
  rw [cartesianKuhnProjectionJet_value]
  exact cartesianKuhnReconstructionLp_ae o δ hδ N _

theorem cartesianKuhnProjectionJet_sub (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    cartesianKuhnProjectionJet o δ hδ N (u-v)=
      cartesianKuhnProjectionJet o δ hδ N u-cartesianKuhnProjectionJet o δ hδ N v := by
  apply WeakSobolevJet.value_injective (openCoordinateBox_isOpen _ _)
    (ae_restrict_mem (openCoordinateBox_isOpen _ _).measurableSet)
  rw [map_sub]
  apply Lp.ext
  filter_upwards [cartesianKuhnProjectionJet_ae o δ hδ N (u-v),
    cartesianKuhnProjectionJet_ae o δ hδ N u,cartesianKuhnProjectionJet_ae o δ hδ N v,
    Lp.coeFn_sub (WeakSobolevJet.value (cartesianKuhnProjectionJet o δ hδ N u))
      (WeakSobolevJet.value (cartesianKuhnProjectionJet o δ hδ N v))] with x h1 h2 h3 h4
  rw [h1,h4]
  exact (cartesianKuhnProjection_sub o δ hδ N u v x).trans (by rw [Pi.sub_apply,h2,h3])

def cartesianKuhnErrorJet (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
      (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  u-cartesianKuhnProjectionJet o δ hδ N (WeakSobolevJet.value u)

theorem cartesianKuhnErrorJet_sub (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (u v : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
      (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :
    cartesianKuhnErrorJet o δ hδ N (u-v)=cartesianKuhnErrorJet o δ hδ N u-cartesianKuhnErrorJet o δ hδ N v := by
  simp only [cartesianKuhnErrorJet,map_sub,cartesianKuhnProjectionJet_sub]
  abel

theorem cartesianKuhnErrorJet_value_local_invariant (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N)
    (u p : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
      (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
    (hp : WeakSobolevJet.value p =ᵐ[volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)]
      cartesianKuhnProjection o δ hδ N (WeakSobolevJet.value p)) :
    WeakSobolevJet.value (cartesianKuhnErrorJet o δ hδ N u) =ᵐ[volume.restrict
      (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)]
      WeakSobolevJet.value (cartesianKuhnErrorJet o δ hδ N (u-p)) := by
  let hKS := (cartesianKuhnPartition o δ hδ N).cell_measure_le_domain
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) i
  have hz : WeakSobolevJet.value (cartesianKuhnErrorJet o δ hδ N p) =ᵐ[volume.restrict
      (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)] (fun _ => 0) := by
    simp only [cartesianKuhnErrorJet,map_sub]
    filter_upwards [hp,(cartesianKuhnProjectionJet_ae o δ hδ N (WeakSobolevJet.value p)).filter_mono (ae_mono hKS),
      (Lp.coeFn_sub (WeakSobolevJet.value p) (WeakSobolevJet.value (cartesianKuhnProjectionJet o δ hδ N
        (WeakSobolevJet.value p)))).filter_mono (ae_mono hKS)] with x h1 h2 h3
    simp only [h3,Pi.sub_apply,h1,h2,sub_self]
  rw [cartesianKuhnErrorJet_sub,map_sub]
  filter_upwards [hz,(Lp.coeFn_sub (WeakSobolevJet.value (cartesianKuhnErrorJet o δ hδ N u))
    (WeakSobolevJet.value (cartesianKuhnErrorJet o δ hδ N p))).filter_mono (ae_mono hKS)] with x h1 h2
  simp only [h2,Pi.sub_apply,h1,sub_zero]

theorem cartesianKuhnErrorJet_field_local_invariant (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (i : CartesianCellIndex N)
    (u p : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
      (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
    (hp : WeakSobolevJet.value p =ᵐ[volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)]
      cartesianKuhnProjection o δ hδ N (WeakSobolevJet.value p)) (k : Fin 2) :
    WeakSobolevJet.field k (cartesianKuhnErrorJet o δ hδ N u) =ᵐ[volume.restrict
      (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)]
      WeakSobolevJet.field k (cartesianKuhnErrorJet o δ hδ N (u-p)) :=
  (cartesianKuhnPartition o δ hδ N).field_congr_on_cell (openCoordinateBox_isOpen _ _)
    (openCoordinateBox_convex _ _) i _ _ (cartesianKuhnErrorJet_value_local_invariant o δ hδ N i u p hp) k

end Carleman
