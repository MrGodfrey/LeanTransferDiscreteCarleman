module
public import Carleman.Spatial.FiniteStrongH2Density
public import Carleman.Spatial.ClassicalConvexHessian
/-! The actual classical convex Hessian inequality passes through full strong
H² density to the original weak state, with an exhaustion-independent constant. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem realLp_norm_sq_of_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (v : Lp ℝ 2 μ) {f : X → ℝ} (hv : v=ᵐ[μ] f) : ‖v‖^2=∫ x, (f x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,hx]

namespace SpatialTest

theorem allOrderJetOn_component_two_smoothD_ae (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) (i j : Fin d) :
    derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 (φ.allOrderJetOn S 2))
      =ᵐ[volume.restrict S] smoothD (EuclideanSpace.basisFun (Fin d) ℝ j)
        (smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) φ.value) := by
  rw [allOrderJetOn_component φ S 2 2 (Sym.cons j (Sym.cons i Sym.nil)),multiTest_cons,multiTest_cons,multiTest_nil,derivativeTest_toLp]
  exact (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp_ae
    (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)

theorem allOrderJetOn_negativeLaplacian (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) :
    negativeLaplacian (φ.allOrderJetOn S 2)= -φ.laplacianOnLp S := by
  rw [negativeLaplacian_apply]
  apply congrArg Neg.neg
  change (∑ i : Fin d, _) = ∑ i : Fin d, _
  apply Finset.sum_congr rfl
  intro i _
  rw [allOrderJetOn_component φ S 2 2 (Sym.cons i (Sym.cons i Sym.nil)),multiTest_cons,multiTest_cons,multiTest_nil,derivativeTest_toLp]

theorem allOrderJetOn_negativeLaplacian_norm_sq (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (S : Set (SpatialCoordinates d)) :
    ‖negativeLaplacian (φ.allOrderJetOn S 2)‖^2=∫ x in S, (spatialLaplacian φ.value x)^2 := by
  rw [allOrderJetOn_negativeLaplacian,norm_neg]
  exact realLp_norm_sq_of_ae _ (φ.laplacianOnLp_ae S)

theorem allOrderJetOn_component_sq_le_hessian (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hb : Bornology.IsBounded S) (α : Sym (Fin d) 2) :
    ‖derivativeComponent α (WeakSobolevJet.field 2 (φ.allOrderJetOn S 2))‖^2≤
      ∫ x in S, smoothHessianSq φ.value x := by
  obtain ⟨j,β,rfl⟩ := Sym.exists_eq_cons_of_succ α
  obtain ⟨i,γ,rfl⟩ := Sym.exists_eq_cons_of_succ β
  have hγ : γ=Sym.nil := Subsingleton.elim _ _
  subst γ
  rw [realLp_norm_sq_of_ae _ (φ.allOrderJetOn_component_two_smoothD_ae S i j)]
  have hi : IntegrableOn (fun x => (smoothD (EuclideanSpace.basisFun (Fin d) ℝ j)
      (smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) φ.value) x)^2) S volume :=
    (ContinuousOn.integrableOn_compact hb.isCompact_closure
      ((smoothD_contDiff (smoothD_contDiff φ.smooth _) _).pow 2).continuous.continuousOn).mono_set subset_closure
  have hh : IntegrableOn (smoothHessianSq φ.value) S volume :=
    (ContinuousOn.integrableOn_compact hb.isCompact_closure
      (smoothHessianSq_contDiff φ.value φ.smooth).continuous.continuousOn).mono_set subset_closure
  apply integral_mono hi hh
  intro x
  calc
    _ ≤ ∑ k : Fin d, (smoothD (EuclideanSpace.basisFun (Fin d) ℝ j)
        (smoothD (EuclideanSpace.basisFun (Fin d) ℝ k) φ.value) x)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ l : Fin d, ∑ k : Fin d, (smoothD (EuclideanSpace.basisFun (Fin d) ℝ l)
        (smoothD (EuclideanSpace.basisFun (Fin d) ℝ k) φ.value) x)^2 :=
      Finset.single_le_sum (f := fun l : Fin d => ∑ k : Fin d,
        (smoothD (EuclideanSpace.basisFun (Fin d) ℝ l)
          (smoothD (EuclideanSpace.basisFun (Fin d) ℝ k) φ.value) x)^2)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ j)

theorem allOrderJetOn_hessian_bound_of_classical (φ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hb : Bornology.IsBounded S)
    (hclass : (∫ x in S, smoothHessianSq φ.value x)≤∫ x in S, (spatialLaplacian φ.value x)^2) :
    ‖WeakSobolevJet.field 2 (φ.allOrderJetOn S 2)‖^2≤
      (Fintype.card (Sym (Fin d) 2) : ℝ)*‖negativeLaplacian (φ.allOrderJetOn S 2)‖^2 := by
  rw [derivativeField_norm_sq]
  calc
    _ ≤ ∑ _α : Sym (Fin d) 2, ‖negativeLaplacian (φ.allOrderJetOn S 2)‖^2 := by
      apply Finset.sum_le_sum
      intro α _
      rw [allOrderJetOn_negativeLaplacian_norm_sq]
      exact (φ.allOrderJetOn_component_sq_le_hessian hb α).trans hclass
    _ = _ := by simp

end SpatialTest

theorem weak_hessian_bound_of_strong_density
    (hb : Bornology.IsBounded S)
    (hclass : ∀ φ : SpatialTest (univ : Set (SpatialCoordinates d)),
      (∀ x∈frontier S, φ.value x=0) →
      (∫ x in S, smoothHessianSq φ.value x)≤∫ x in S, (spatialLaplacian φ.value x)^2)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) (hu : HasSmoothDirichletH2Approximation u) :
    ‖WeakSobolevJet.field 2 u‖^2≤(Fintype.card (Sym (Fin d) 2) : ℝ)*‖negativeLaplacian u‖^2 := by
  obtain ⟨F,hF,_,ht⟩ := hu
  have hleft := (((WeakSobolevJet.fieldCLM 2).continuous.tendsto u).comp ht).norm.pow 2
  have hright := (((negativeLaplacian (d := d) (S := S)).continuous.tendsto u).comp ht).norm.pow 2
  exact le_of_tendsto_of_tendsto hleft (tendsto_const_nhds.mul hright)
    (Eventually.of_forall fun n => (F n).allOrderJetOn_hessian_bound_of_classical hb (hclass (F n) (hF n)))

theorem halfspaceSmoothInner_weak_hessian_bound {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {z : SpatialCoordinates d} (hz : z∈halfspaceSmoothInner ℓ b n)
    (u : dirichletH2JetSpace (halfspaceSmoothInner ℓ b n)) :
    ‖WeakSobolevJet.field 2 u.val‖^2≤
      (Fintype.card (Sym (Fin d) 2) : ℝ)*‖negativeLaplacian u.val‖^2 :=
  weak_hessian_bound_of_strong_density
    ((halfspaceSmoothInner_compact ℓ b hb n).isBounded.subset subset_closure)
    (fun φ hzφ => halfspaceSmoothInner_classical_hessian_bound ℓ b hb n hz φ.value φ.smooth hzφ)
    u.val (halfspaceSmoothInner_strong_h2_approximation hd ℓ b n hb hz u)

theorem halfspaceSmoothInner_weak_hessian_norm_bound {ι : Type*} [Fintype ι] (hd : 0<d)
    (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    (hb : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {z : SpatialCoordinates d} (hz : z∈halfspaceSmoothInner ℓ b n)
    (u : dirichletH2JetSpace (halfspaceSmoothInner ℓ b n)) :
    ‖WeakSobolevJet.field 2 u.val‖≤
      Real.sqrt (Fintype.card (Sym (Fin d) 2) : ℝ)*‖negativeLaplacian u.val‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  exact halfspaceSmoothInner_weak_hessian_bound hd ℓ b n hb hz u

end Carleman
