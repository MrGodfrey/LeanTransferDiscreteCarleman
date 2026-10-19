module

public import Carleman.Spatial.CartesianPhysicalStiffness
public import Carleman.Spatial.CartesianPhysicalStability
public import Carleman.Spatial.CartesianWeightedTestInterface
public import Carleman.Spatial.CartesianApproximationInterface
public import Carleman.Spatial.CartesianHilbertObservation
public import Carleman.Transfer.OriginalData

/-! Assembly of the original Cartesian N1--N5 data for the actual operators.
The continuous Dirichlet domain H² inclusion is explicitly the original A1
input; it is not assumed proved by this numerical assembly. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2400000
open MeasureTheory Set
namespace Carleman
attribute [local instance] Classical.propDecidable

def cartesianErrorScales (C h : ℝ) (hC : 0 ≤ C) (hh : 0 ≤ h) : ErrorScales where
  aE := C*h
  a₀ := C*h^2
  ηA := 0
  aE_nonneg := mul_nonneg hC hh
  a₀_nonneg := mul_nonneg hC (sq_nonneg h)
  ηA_nonneg := le_rfl

theorem cartesian_numericalData {d : ℕ} {S : Set (SpatialCoordinates (d+1))}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 2 ρ.value (closure S))
    (κ β τStar : ℝ) (hκ : 1 ≤ κ) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (ω₀ ω : Set (SpatialCoordinates (d+1))) (hω₀ : MeasurableSet ω₀)
    (hcompact₀ : IsCompact (closure ω₀)) (hω : IsOpen ω) (hinc : closure ω₀ ⊆ ω) :
    let a := boundedDirichletOriginalForm hS (Nat.succ_pos d)
      (hcompact.isBounded.subset subset_closure)
    ∃ ε > (0:ℝ), ε ≤ 1 ∧ ∃ Ctime > (0:ℝ), ∃ Csuper > (0:ℝ),
      ∃ (Capp : ℝ) (hCa : 0 < Capp), ∃ Cnum > (0:ℝ),
    ∀ (o δ : Fin (d+1) → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin (d+1) → ℕ)
      (hdom : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)=S) (h : ℝ) (hh : 0 < h),
      (∀ j, h/κ ≤ δ j) → (∀ j, δ j ≤ h) →
    ∀ (hD : a.model.domain ≤ sobolevSubspace (d+1) (2*1) (volume.restrict S) S)
      (w : TimeWeight) (g : TimeGrid) (_H : TimeWeightRegularity w g β), h*w.max ≤ ε →
    Nonempty (Section5.NumericalData a hD
      (show Reconstruction (dirichletSubspace S) (CartesianPhysicalState δ hδ N) from
        hdom ▸ cartesianReconstruction o δ hδ N)
      (cartesianPhysicalLaplacian o δ hδ N).toLinearMap 0
      (by subst S; exact cartesianLoadInterface o δ hδ N)
      (cartesianPhysicalControlExtension o δ hδ N ω).adjoint.toLinearMap
      g w ρ ω₀ hω₀
      (fun t => cartesianStateSeminorm o δ hδ N (ρ.multiplier w 0 t).value)
      (fun t => cartesianStateSeminorm o δ hδ N (ρ.multiplier w 0 t).value)
      (fun t => cartesianControlSeminorm o δ hδ N ω (ρ.multiplier w 0 t).value)
      τStar Ctime Csuper Cnum h (cartesianErrorScales Capp h hCa.le hh.le)) := by
  classical
  dsimp only
  have hρ₁ := hρ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  obtain ⟨ε,hε,he1,Ctime,hCt,Csuper,hCs,htest⟩ :=
    cartesian_weightedTest_interface hS hc hcompact ρ hρ κ β τStar (lt_of_lt_of_le zero_lt_one hκ) hβ hτStar
  obtain ⟨Capp,hCa,happrox⟩ := cartesian_weightedApproximation_interface hS hc hcompact ρ hρ₁ κ hκ
  obtain ⟨Cm,hCm,hmass⟩ := allowed_weight_cartesian_physical_stability hS hc hcompact ρ hρ₁
  obtain ⟨h₀,hh₀,Co,hCo,hobs⟩ := allowed_weight_cartesian_hilbert_observation
    hS hc hcompact ρ hρ₁ ω₀ ω hω₀ hcompact₀ hω hinc
  refine ⟨min ε h₀,lt_min hε hh₀,(min_le_left _ _).trans he1,
    Ctime,hCt,Csuper,hCs,Capp,hCa,Cm+Co^2,by positivity,?_⟩
  intro o δ hδ N hdom h hh hlower hupper hD w g H hsmall
  subst S
  let a := boundedDirichletOriginalForm hS (Nat.succ_pos d)
    (hcompact.isBounded.subset subset_closure)
  have hmε : h*w.max ≤ ε := hsmall.trans (min_le_left _ _)
  have hm1 : h*w.max ≤ 1 := hmε.trans he1
  have hh₀' : h ≤ h₀ := by
    have hmax : 1 ≤ w.max := (w.lower 0).trans (w.upper 0)
    have hp := mul_le_mul_of_nonneg_left hmax hh.le
    have hp' : h ≤ h*w.max := by simpa only [mul_one] using hp
    exact hp'.trans (hsmall.trans (min_le_right _ _))
  have hqt (t : ℝ) : h*w.q t ≤ 1 := (mul_le_mul_of_nonneg_left (w.upper t) hh.le).trans hm1
  have hsigned (e : Bool) : ∃ η : ℝ, |η|=1 ∧ ρ.scaled η=ρ.signed e := by
    cases e
    · exact ⟨1,abs_one,ρ.scaled_one⟩
    · exact ⟨-1,by norm_num,ρ.scaled_neg_one⟩
  have hb (t : ℝ) (f : CartesianPhysicalState δ hδ N) :=
    hmass o δ hδ N (Subset.refl _) h hh hupper w 0 t 1 (by norm_num) (hqt t) f
  simp only [SpatialProfile.scaled_one] at hb
  refine ⟨{
    stiffness := by
      intro z v
      simp only [LinearMap.zero_apply,add_zero]
      exact cartesianPhysicalLaplacian_stiffness (Nat.succ_pos d) o δ hδ N z v
    approximation := by
      intro e τ _
      obtain ⟨η,hη,he⟩ := hsigned e
      rw [← he]
      exact happrox o δ hδ N rfl h hh hlower hupper a.model.domain hD a.domain_le w g τ η hη hm1
    test := fun e τ hτ => by
      let η := Classical.choose (hsigned e)
      have hη := (Classical.choose_spec (hsigned e)).1
      have he := (Classical.choose_spec (hsigned e)).2
      rw [← he]
      exact Classical.choose (htest o δ hδ N rfl h hh hlower hupper w g H τ η hτ hη hmε)
    defect := by intros; simp only [LinearMap.zero_apply,abs_zero,cartesianErrorScales,zero_mul,le_refl]
    reconstruction_upper := by
      intro i f
      exact (hb (g.nodeTime i) f).2.1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg Co)) (sq_nonneg _))
    reconstruction_lower := by
      intro i f
      exact (hb (g.nodeTime i) f).1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg Co)) (sq_nonneg _))
    lift_bound := by
      intro i f
      exact (hb (g.nodeTime i) f).2.2.1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg Co)) (sq_nonneg _))
    observation_bound := by
      intro i f
      have ho := hobs o δ hδ N (Subset.refl _) h hh hh₀' hupper w 0 (g.nodeTime i) 1
        (by norm_num) (hqt (g.nodeTime i)) f
      simp only [SpatialProfile.scaled_one] at ho
      have hs := sq_le_sq₀ (apply_nonneg _ _) (mul_nonneg hCo.le (norm_nonneg _)) |>.mpr ho
      rw [mul_pow] at hs
      exact hs.trans (mul_le_mul_of_nonneg_right (by linarith only [hCm] : Co^2 ≤ Cm+Co^2) (sq_nonneg _)) }⟩

end Carleman
