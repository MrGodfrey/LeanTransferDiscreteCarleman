module

public import Carleman.Spatial.BoxDirichletRegularity
public import Carleman.Weights.DirichletAllowedData
public import Carleman.Section3.OriginalWeights

/-! The original box Dirichlet operator supplies the full spatial analytic
data, with its canonical H2 jet and constants chosen before all time weights. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2400000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem box_dirichlet_graph_estimate (hd : 0 < d) (lo hi : Fin d → ℝ)
    (hpos : ∀ i, lo i < hi i) :
    let hS := openCoordinateBox_isOpen lo hi
    let a := boundedDirichletOriginalForm hS hd (openCoordinateBox_isBounded lo hi)
    let hD := box_dirichlet_domain_le_h2 hd lo hi hpos
    ∃ Creg > (0:ℝ), ∀ z : a.model.domain,
      ‖domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z‖ ≤ Creg*‖a.model.operator z‖ := by
  dsimp only
  obtain ⟨K,hK,hreg⟩ := exists_box_dirichlet_H2_estimate hd lo hi hpos
  refine ⟨max 1 K,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z
  let hS := openCoordinateBox_isOpen lo hi
  let a := boundedDirichletOriginalForm hS hd (openCoordinateBox_isBounded lo hi)
  obtain ⟨u,huz,hu,huf⟩ := (dirichlet_operator_graph_iff hS hd
    (openCoordinateBox_isBounded lo hi) (z : Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi)))
      (a.model.operator z)).mp ⟨z,rfl,rfl⟩
  obtain ⟨v,hv,_,hvn⟩ := hreg u hu (a.model.operator z) huf
  have he : v=domainSobolevJet hS (ae_restrict_mem hS.measurableSet)
      (box_dirichlet_domain_le_h2 hd lo hi hpos) z := by
    apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
    rw [domainSobolevJet_value]
    exact (congrArg (fun j => WeakSobolevJet.value j) hv).trans huz
  rw [he] at hvn
  exact hvn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem box_analytic_data_uniform (hd : 0 < d) (lo hi : Fin d → ℝ)
    (hpos : ∀ i, lo i < hi i)
    (ρ : SpatialProfile (volume.restrict (openCoordinateBox lo hi)))
    (hρ : SmoothOnClosure ρ.value (openCoordinateBox lo hi)) :
    let hS := openCoordinateBox_isOpen lo hi
    let a := boundedDirichletOriginalForm hS hd (openCoordinateBox_isBounded lo hi)
    let hD := box_dirichlet_domain_le_h2 hd lo hi hpos
    ∃ Creg > (0:ℝ), ∃ C Ccomm : ℝ, 1 ≤ C ∧ 0 < Ccomm ∧
      (∀ z : a.model.domain,
        ‖domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z‖ ≤ Creg*‖a.model.operator z‖) ∧
      ∀ (w : TimeWeight) (τStar : ℝ),
        Section3.AllowedFamily hS (ae_restrict_mem hS.measurableSet)
          (dirichletSubspace_sobolev (openCoordinateBox lo hi)) hD
          a.scalarForm a.model.operator ρ w (1/2) C Ccomm τStar := by
  dsimp only
  obtain ⟨Creg,hCr,hreg⟩ := box_dirichlet_graph_estimate hd lo hi hpos
  obtain ⟨C,Ccomm,hC,hCc,hfamily⟩ := dirichlet_allowed_family_uniform
    (openCoordinateBox_isOpen lo hi) hd (openCoordinateBox_isBounded lo hi) ρ hρ
  exact ⟨Creg,hCr,C,Ccomm,hC,hCc,hreg,
    fun w τStar => hfamily (box_dirichlet_domain_le_h2 hd lo hi hpos) w τStar⟩

theorem box_analytic_realization (hd : 0 < d) (lo hi : Fin d → ℝ)
    (hpos : ∀ i, lo i < hi i) (f : SpatialCoordinates d → ℝ)
    (hf : SmoothOnClosure f (openCoordinateBox lo hi)) :
    let hS := openCoordinateBox_isOpen lo hi
    let a := boundedDirichletOriginalForm hS hd (openCoordinateBox_isBounded lo hi)
    let hD := box_dirichlet_domain_le_h2 hd lo hi hpos
    ∃ ρ : SpatialProfile (volume.restrict (openCoordinateBox lo hi)), ρ.value=f ∧
      ∃ Creg > (0:ℝ), ∃ C Ccomm : ℝ, 1 ≤ C ∧ 0 < Ccomm ∧
      (∀ z : a.model.domain,
        ‖domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z‖ ≤ Creg*‖a.model.operator z‖) ∧
      ∀ (w : TimeWeight) (τStar : ℝ),
        Section3.AllowedFamily hS (ae_restrict_mem hS.measurableSet)
          (dirichletSubspace_sobolev (openCoordinateBox lo hi)) hD
          a.scalarForm a.model.operator ρ w (1/2) C Ccomm τStar := by
  obtain ⟨ρ,hρ⟩ := exists_profile_of_smooth (openCoordinateBox_isOpen lo hi)
    (openCoordinateBox_isBounded lo hi) f hf
  exact ⟨ρ,hρ,box_analytic_data_uniform hd lo hi hpos ρ (by rwa [hρ])⟩

end Carleman
