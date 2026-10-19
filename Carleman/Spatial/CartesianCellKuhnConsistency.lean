module

public import Carleman.Geometry.CoordinateHyperplaneNull
public import Carleman.Spatial.CartesianCellNearestValue
public import Carleman.Spatial.CartesianCellControlSupport
public import Carleman.Spatial.CartesianKuhnReconstructionJet
public import Carleman.Spatial.DerivativeFiberNorm
public import Carleman.Spatial.NodalWeightedNorm

/-! The original E_h and R_h differ by O(h) times the actual weak-gradient norm, including the strip. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianCell_kuhn_pointwise_consistency : ∃ C > (0:ℝ),
    ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (h : ℝ) (_hh : 0 ≤ h) (_hstep : ∀ j, δ j ≤ h) (f : CartesianInteriorIndex N → ℝ),
    ∀ᵐ x ∂volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      |finiteCellFunction (cartesianDualCell o δ N) f x-cartesianKuhnReconstruction o δ hδ N f x| ≤
        C*h*‖WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f) x‖ := by
  obtain ⟨R,hR,hreverse⟩ := derivativeOneFiber_reverse_bound (d := d)
  refine ⟨R*(d:ℝ)+1,by positivity,?_⟩
  intro o δ hδ N h hh hstep f
  apply (cartesianKuhnPartition o δ hδ N).ae_of_cells (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _)
  intro i
  let z := (cartesianCellLatticeIndex N i).1
  let S := cartesianFiniteSimplex o δ hδ N i
  let p := simplexNodalInterpolant S (fun k => cartesianInteriorData o δ N f (S.points k))
  filter_upwards [cartesianKuhnSimplex_nearest_vertex_ae o δ hδ z i.2,
    cartesianKuhnReconstructionJet_gradient_on_cell o δ hδ N f i,
    ae_restrict_mem (simplicialCell_measurable S.points)] with x hn hg hx
  obtain ⟨k,hk⟩ := hn
  change ∀ j, |x j-S.points k j| < δ j/2 at hk
  have hv : S.points k=cartesianGridPoint o δ (kuhnVertexIndex z i.2 k) :=
    cartesianKuhnSimplex_points_eq_gridPoint o δ hδ z i.2 k
  have hE : finiteCellFunction (cartesianDualCell o δ N) f x=p (S.points k) := by
    have he := cartesianCellFunction_nearest_value o δ hδ N f (kuhnVertexIndex z i.2 k) x
      (by intro j; rw [← hv]; exact hk j)
    rw [← hv] at he
    exact he.trans (simplexNodalInterpolant_vertex S
      (fun l => cartesianInteriorData o δ N f (S.points l)) k).symm
  have hdist : dist (S.points k) x ≤ (d:ℝ)*h := by
    rw [dist_comm]
    apply closedCoordinateBox_diameter_bound
      (fun j => S.points k j-δ j/2) (fun j => S.points k j+δ j/2)
      (fun j => by linarith [hδ j]) h hh (fun j => by linarith [hstep j])
    · intro j
      have he := abs_lt.mp (hk j)
      constructor <;> linarith
    · intro j
      constructor <;> linarith [hδ j]
  have hRx : cartesianKuhnReconstruction o δ hδ N f x=p x :=
    cartesianKuhnReconstruction_on_cell o δ hδ N f i hx
  change WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f) x=
    derivativeOneFiber (fderiv ℝ p x) at hg
  rw [(affineScalar_hasFDerivAt p x).fderiv] at hg
  rw [hE,hRx,hg]
  have hl : |p (S.points k)-p x| ≤ ‖affineScalarDerivative p‖*dist (S.points k) x :=
    (affineScalar_lipschitz p).dist_le_mul _ _
  calc
    _ ≤ ‖affineScalarDerivative p‖*dist (S.points k) x := hl
    _ ≤ (R*‖derivativeOneFiber (affineScalarDerivative p)‖)*((d:ℝ)*h) :=
      mul_le_mul (hreverse _) hdist (dist_nonneg) (mul_nonneg hR.le (norm_nonneg _))
    _ = (R*(d:ℝ))*h*‖derivativeOneFiber (affineScalarDerivative p)‖ := by ring
    _ ≤ _ := by gcongr; linarith

theorem cartesianCell_kuhn_L2_consistency : ∃ C > (0:ℝ),
    ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (h : ℝ) (_hh : 0 ≤ h) (_hstep : ∀ j, δ j ≤ h) (f : CartesianPhysicalState δ hδ N),
      ‖cartesianCellIsometry o δ hδ N f-cartesianKuhnReconstructionLp o δ hδ N f‖ ≤
        C*h*‖WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f)‖ := by
  obtain ⟨C,hC,hpoint⟩ := cartesianCell_kuhn_pointwise_consistency (d := d)
  refine ⟨C,hC,?_⟩
  intro o δ hδ N h hh hstep f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (cartesianCellIsometry o δ hδ N f) (cartesianKuhnReconstructionLp o δ hδ N f),
    cartesianCellIsometry_ae o δ hδ N f,cartesianKuhnReconstructionLp_ae o δ hδ N f,
    hpoint o δ hδ N h hh hstep f] with x hs he hr hp
  rw [hs]
  simp only [Pi.sub_apply,he,hr,Real.norm_eq_abs]
  exact hp

end Carleman
