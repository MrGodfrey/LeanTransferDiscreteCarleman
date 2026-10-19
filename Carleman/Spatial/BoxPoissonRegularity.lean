module

public import Carleman.Spatial.FiniteBoxPoissonExtension
public import Carleman.Spatial.InteriorPoissonRegularity

/-! Global H2 regularity of the original weak Dirichlet Poisson solution
on an arbitrary coordinate box, by actual finite odd extension and interior regularity. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem derivativeComponent_norm_le_field {k : ℕ} {ν : Measure (SpatialCoordinates d)}
    (α : Sym (Fin d) k) (u : Lp (DerivativeFiber d k) 2 ν) : ‖derivativeComponent α u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [derivativeComponent_ae α u] with x hx
  rw [hx]
  exact PiLp.norm_apply_le _ _

theorem exists_box_dirichlet_H2_bound (a b : Fin d → ℝ) (hpos : ∀ i, a i < b i) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)),
      u ∈ dirichletJetSpace (openCoordinateBox a b) →
      ∀ f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b)), IsWeakNegativeLaplacian u f →
      ∃ v : WeakSobolevJet d 2 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b),
        WeakSobolevJet.truncate (by decide : 1 ≤ 2) v=u ∧ negativeLaplacian v=f ∧
        ‖WeakSobolevJet.field 2 v‖^2 ≤ C*(‖f‖+‖WeakSobolevJet.field 1 u‖+‖WeakSobolevJet.value u‖)^2 := by
  obtain ⟨M,hM,hbound⟩ := exists_interior_H2_bound
    (openCoordinateBox_isOpen (expandedBoxLower a b Finset.univ) (expandedBoxUpper a b Finset.univ))
    (openCoordinateBox_isOpen a b) (openCoordinateBox_isBounded a b).isCompact_closure
    (expandedBox_closure_inside a b hpos)
  refine ⟨(Fintype.card (Sym (Fin d) 2):ℝ)*(M*4^d*(1+2*(d:ℝ)))^2,by positivity,?_⟩
  intro u hu f hf
  obtain ⟨U,F,hU⟩ := exists_finite_box_extension a b hpos Finset.univ u hu f hf
  rcases hU with ⟨hU0,hUP,hUu,hF,hV,hG⟩
  simp only [Finset.card_univ,Fintype.card_fin] at hF hV hG
  obtain ⟨v,hv,hvf,hvn⟩ := hbound U F hUP
  have hvu : WeakSobolevJet.truncate (by decide : 1 ≤ 2) v=u := hv.trans hUu
  have hveq : negativeLaplacian v=f := by
    have hw := negativeLaplacian_isWeak v
    rw [hvu] at hw
    exact hw.unique_rhs (openCoordinateBox_isOpen a b) hf
  refine ⟨v,hvu,hveq,?_⟩
  have hsum : (∑ i : Fin d, ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 U)‖) ≤
      (d:ℝ)*(4^d*‖WeakSobolevJet.field 1 u‖) := by
    calc
      _ ≤ ∑ _i : Fin d, ‖WeakSobolevJet.field 1 U‖ :=
        Finset.sum_le_sum fun i _ => derivativeComponent_norm_le_field _ _
      _ = (d:ℝ)*‖WeakSobolevJet.field 1 U‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg d)
  have hb : ‖F‖+2*(∑ i : Fin d, ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 U)‖)+
      ‖WeakSobolevJet.value U‖ ≤
      (4:ℝ)^d*(1+2*(d:ℝ))*(‖f‖+‖WeakSobolevJet.field 1 u‖+‖WeakSobolevJet.value u‖) := by
    have hnF := mul_nonneg (Nat.cast_nonneg d) (norm_nonneg f)
    have hnV := mul_nonneg (Nat.cast_nonneg d) (norm_nonneg (WeakSobolevJet.value u))
    have hnG := norm_nonneg (WeakSobolevJet.field 1 u)
    have hp : (0:ℝ) ≤ 4^d := by positivity
    nlinarith [mul_nonneg hp hnF,mul_nonneg hp hnV,mul_nonneg hp hnG]
  have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr (mul_le_mul_of_nonneg_left hb hM)
  have hh := hvn.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (Fintype.card (Sym (Fin d) 2))))
  convert hh using 1
  ring

end Carleman
