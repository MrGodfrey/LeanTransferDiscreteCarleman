module

public import Carleman.Geometry.BoxLipschitzDomain
public import Carleman.Spatial.BoxAnalyticData
public import Carleman.Section3.Complete

/-! All original Section 3 auxiliary estimates on an actual positive box:
geometry, regularity and the entire allowed family are supplied internally. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2400000
open MeasureTheory Set
namespace Carleman

theorem box_section3 {d : ℕ} (lo hi : Fin (d+1) → ℝ) (hpos : ∀ i, lo i < hi i)
    (ρ : SpatialProfile (volume.restrict (openCoordinateBox lo hi)))
    (hρ : SmoothOnClosure ρ.value (openCoordinateBox lo hi))
    (β τStar : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    let hS := openCoordinateBox_isOpen lo hi
    let a := boundedDirichletOriginalForm hS (Nat.succ_pos d) (openCoordinateBox_isBounded lo hi)
    let hD := box_dirichlet_domain_le_h2 (Nat.succ_pos d) lo hi hpos
    ∃ C Ccomm : ℝ, 1 ≤ C ∧ 0 < Ccomm ∧
      (∀ w : TimeWeight,
        Section3.AllowedFamily hS (ae_restrict_mem hS.measurableSet) a.sobolev hD
          a.scalarForm a.model.operator ρ w (1/2) C Ccomm τStar) ∧
      ∃ K : ℝ, 0 < K ∧ ∃ (L₀ : ℝ → ℝ) (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧
        Section3.Conclusions hS (ae_restrict_mem hS.measurableSet) a.model
          a.sobolev a.domain_le hD a.scalarForm ρ (1/2) C Ccomm β τStar K L₀ δ := by
  dsimp only
  obtain ⟨Creg,hCr,C,Ccomm,hC,hCc,hreg,hfamily⟩ :=
    box_analytic_data_uniform (Nat.succ_pos d) lo hi hpos ρ hρ
  let hS := openCoordinateBox_isOpen lo hi
  let a := boundedDirichletOriginalForm hS (Nat.succ_pos d) (openCoordinateBox_isBounded lo hi)
  refine ⟨C,Ccomm,hC,hCc,(fun w => hfamily w τStar),?_⟩
  exact a.section3 (openCoordinateBox_bounded_lipschitz lo hi hpos)
    (box_dirichlet_domain_le_h2 (Nat.succ_pos d) lo hi hpos) ρ hρ (by decide)
    Creg (1/2) C Ccomm β τStar (by norm_num) (zero_le_one.trans hC) hCc.le hβ hτStar hreg

end Carleman
