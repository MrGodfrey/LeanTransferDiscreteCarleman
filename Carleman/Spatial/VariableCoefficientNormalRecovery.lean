module
public import Carleman.Spatial.VariableCoefficientDifference
public import Carleman.Spatial.WeakProduct
public import Carleman.Spatial.MultiplierAlgebra
public import Carleman.Spatial.CellwiseInverseWeight
/-! Actual normal-flux recovery for divergence-form equations. The normal
second derivative is constructed from the original weak equation, the
previously proved tangential estimates, and multiplication by the actual
reciprocal coefficient. The final half-space theorem assumes only the
original H¹₀ weak solution, global bounded Lipschitz elliptic coefficients
which are smooth on the half-space, and an L² load. Its constants are
explicit and independent of difference-quotient steps. This does not yet
provide nonlinear boundary pullback or general-polytope regularity. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
namespace BoundedMultiplier
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

def reciprocal (a : BoundedMultiplier ν) {κ : ℝ} (hκ : 0 < κ)
    (ha : ∀ᵐ x ∂ν, κ ≤ |a.value x|) : BoundedMultiplier ν where
  value x := (a.value x)⁻¹
  measurable := a.measurable.inv₀
  bound := κ⁻¹
  bound_nonneg := by positivity
  bounded := by
    filter_upwards [ha] with x hx
    rw [abs_inv]
    exact inv_anti₀ hκ hx

def reciprocalDerivative (a da : BoundedMultiplier ν) {κ : ℝ} (hκ : 0 < κ)
    (ha : ∀ᵐ x ∂ν, κ ≤ |a.value x|) : BoundedMultiplier ν where
  value x := -((a.value x)⁻¹)^2 * da.value x
  measurable := (a.measurable.inv₀.pow 2).neg.mul da.measurable
  bound := (κ⁻¹)^2 * da.bound
  bound_nonneg := mul_nonneg (sq_nonneg _) da.bound_nonneg
  bounded := by
    filter_upwards [(a.reciprocal hκ ha).bounded,da.bounded] with x hx hd
    rw [abs_mul,abs_neg,abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx 2) hd (abs_nonneg _) (by positivity)

end BoundedMultiplier
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def BoundedMultiplier.spatialDerivativeOn (a : BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    (hS : IsOpen S) (ha : ContDiffOn ℝ ∞ a.value S) {C : NNReal}
    (hC : LipschitzWith C a.value) (j : Fin d) : BoundedMultiplier (volume.restrict S) where
  value x := fderiv ℝ a.value x (EuclideanSpace.basisFun (Fin d) ℝ j)
  measurable := ((ha.continuousOn_fderiv_of_isOpen hS (by simp)).clm_apply continuousOn_const).aestronglyMeasurable hS.measurableSet
  bound := C
  bound_nonneg := C.coe_nonneg
  bounded := Eventually.of_forall fun x => by
    have hb := (fderiv ℝ a.value x).le_opNorm (EuclideanSpace.basisFun (Fin d) ℝ j)
    rw [Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one j,mul_one] at hb
    exact hb.trans (norm_fderiv_le_of_lipschitz ℝ hC)

theorem matrix_elliptic_diagonal (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    {C : Fin d → Fin d → NNReal} (hC : ∀ i j, LipschitzWith (C i j) (a i j).value)
    (κ : ℝ) (hA : ∀ᵐ x ∂volume, ∀ ξ : Fin d → ℝ,
      κ*(∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, (a i j).value x*(ξ i)*(ξ j))
    (r : Fin d) (x : SpatialCoordinates d) : κ ≤ (a r r).value x := by
  classical
  have hae : ∀ᵐ y ∂volume, κ ≤ (a r r).value y := by
    filter_upwards [hA] with y hy
    simpa using hy (fun i => if i=r then 1 else 0)
  have hc : IsClosed {y | κ ≤ (a r r).value y} := isClosed_le continuous_const (hC r r).continuous
  have he : {y | κ ≤ (a r r).value y}=univ := hc.ae_eq_univ_iff_eq.mp
    (hae.mono fun y hy => propext (iff_of_true hy (mem_univ y)))
  have hx : x ∈ {y | κ ≤ (a r r).value y} := by rw [he]; exact mem_univ x
  exact hx

theorem weak_derivative_divide_coefficient (hS : IsOpen S)
    (a da : BoundedMultiplier (volume.restrict S))
    (ha : ContDiffOn ℝ ∞ a.value S) (e : SpatialCoordinates d)
    (hda : da.value =ᵐ[volume.restrict S] fun x => fderiv ℝ a.value x e)
    {κ : ℝ} (hκ : 0 < κ) (hpos : ∀ x ∈ S, κ ≤ |a.value x|)
    (g v : Lp ℝ 2 (volume.restrict S))
    (hv : IsWeakSpatialDerivative (volume.restrict S) S e (a.map g) v) :
    ∃ w, IsWeakSpatialDerivative (volume.restrict S) S e g w ∧
      ‖w‖ ≤ κ⁻¹*‖v‖+(κ⁻¹)^2*da.bound*a.bound*‖g‖ := by
  have hp : ∀ᵐ x ∂volume.restrict S, κ ≤ |a.value x| :=
    (ae_restrict_mem hS.measurableSet).mono fun x hx => hpos x hx
  have hn (x) (hx : x ∈ S) : a.value x ≠ 0 := abs_pos.mp (hκ.trans_le (hpos x hx))
  let b := a.reciprocal hκ hp
  let db := a.reciprocalDerivative da hκ hp
  have hb : ContDiffOn ℝ ∞ b.value S := ha.inv hn
  have hdb : db.value =ᵐ[volume.restrict S] fun x => fderiv ℝ b.value x e := by
    filter_upwards [hda,ae_restrict_mem hS.measurableSet] with x hd hx
    have hdif := (ha.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
    change -((a.value x)⁻¹)^2 * da.value x = fderiv ℝ (fun y => (a.value y)⁻¹) x e
    have hi := ((hasFDerivAt_inv (hn x hx)).comp x hdif.hasFDerivAt).fderiv
    change fderiv ℝ (fun y => (a.value y)⁻¹) x = _ at hi
    rw [hd,hi]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,inv_pow]
    ring
  have hinv : b.map (a.map g)=g := b.map_inverse a (by
    filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
    exact inv_mul_cancel₀ (hn x hx)) g
  have hw := hv.mul hS (ae_restrict_mem hS.measurableSet) b db hb hdb
  rw [hinv] at hw
  refine ⟨_,hw,(norm_add_le _ _).trans ?_⟩
  have h1 := b.seminorm_le v
  have h2 := db.seminorm_le (a.map g)
  have h3 := a.seminorm_le g
  exact add_le_add h1 (h2.trans (by
    change (κ⁻¹)^2*da.bound*‖a.map g‖ ≤ _
    calc
      _ ≤ (κ⁻¹)^2*da.bound*(a.bound*‖g‖) := mul_le_mul_of_nonneg_left h3 (mul_nonneg (sq_nonneg _) da.bound_nonneg)
      _ = _ := by ring))

theorem exists_normal_derivative_of_matrix_equation (hS : IsOpen S)
    (a da : Fin d → Fin d → BoundedMultiplier (volume.restrict S))
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j).value S)
    (hda : ∀ i j, (da i j).value =ᵐ[volume.restrict S]
      fun x => fderiv ℝ (a i j).value x (EuclideanSpace.basisFun (Fin d) ℝ j))
    (r : Fin d) {κ : ℝ} (hκ : 0 < κ) (hpos : ∀ x ∈ S, κ ≤ |(a r r).value x|)
    (G : Fin d → Lp ℝ 2 (volume.restrict S)) (f : Lp ℝ 2 (volume.restrict S))
    (D : Fin d → Fin d → Lp ℝ 2 (volume.restrict S))
    (hD : ∀ i j, (i,j) ≠ (r,r) → IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ j) (G i) (D i j))
    {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hG : ∀ i, ‖G i‖ ≤ M) (hDn : ∀ i j, (i,j) ≠ (r,r) → ‖D i j‖ ≤ K)
    (hf : ∀ φ : SpatialTest S,
      (∑ i, ∑ j, inner ℝ ((a i j).map (G i))
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)))=
      inner ℝ f (φ.toLp (volume.restrict S))) :
    ∃ w, IsWeakSpatialDerivative (volume.restrict S) S
        (EuclideanSpace.basisFun (Fin d) ℝ r) (G r) w ∧
      ‖w‖ ≤ κ⁻¹*(‖f‖+∑ i, ∑ j, ((a i j).bound*K+(da i j).bound*M))+
        (κ⁻¹)^2*(da r r).bound*(a r r).bound*M := by
  classical
  let s := (Finset.univ : Finset (Fin d × Fin d)).erase (r,r)
  let V (p : Fin d × Fin d) := (a p.1 p.2).map (D p.1 p.2)+(da p.1 p.2).map (G p.1)
  let R := -f-∑ p ∈ s, V p
  have hs (p : Fin d × Fin d) (hp : p ∈ s) : p ≠ (r,r) := (Finset.mem_erase.mp hp).1
  have hV (p : Fin d × Fin d) (hp : p ∈ s) : IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ p.2) ((a p.1 p.2).map (G p.1)) (V p) :=
    (hD p.1 p.2 (hs p hp)).mul hS (ae_restrict_mem hS.measurableSet) _ _ (ha _ _) (hda _ _)
  have hR : IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ r) ((a r r).map (G r)) R := by
    intro φ
    let F (p : Fin d × Fin d) := inner ℝ ((a p.1 p.2).map (G p.1))
      (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ p.2))
    have hall : (∑ p : Fin d × Fin d, F p)=inner ℝ f (φ.toLp (volume.restrict S)) := by
      simpa only [Fintype.sum_prod_type] using hf φ
    have he := Finset.sum_erase_add Finset.univ F (Finset.mem_univ (r,r))
    have heq : (∑ p ∈ s, F p)= -(∑ p ∈ s, inner ℝ (V p) (φ.toLp (volume.restrict S))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p hp => hV p hp φ
    change F (r,r)= -inner ℝ (-f-∑ p ∈ s, V p) (φ.toLp (volume.restrict S))
    rw [inner_sub_left,inner_neg_left,sum_inner]
    change (∑ p ∈ s, F p)+F (r,r)=_ at he
    rw [heq,hall] at he
    linarith
  have hVn (p : Fin d × Fin d) (hp : p ∈ s) :
      ‖V p‖ ≤ (a p.1 p.2).bound*K+(da p.1 p.2).bound*M := by
    exact (norm_add_le _ _).trans (add_le_add
      ((a _ _).seminorm_le _ |>.trans (mul_le_mul_of_nonneg_left (hDn _ _ (hs p hp)) (a _ _).bound_nonneg))
      ((da _ _).seminorm_le _ |>.trans (mul_le_mul_of_nonneg_left (hG _) (da _ _).bound_nonneg)))
  have hRn : ‖R‖ ≤ ‖f‖+∑ i, ∑ j, ((a i j).bound*K+(da i j).bound*M) := by
    apply (norm_sub_le _ _).trans
    rw [norm_neg]
    refine add_le_add le_rfl ?_
    calc
      _ ≤ ∑ p ∈ s, ‖V p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ s, ((a p.1 p.2).bound*K+(da p.1 p.2).bound*M) := Finset.sum_le_sum hVn
      _ ≤ ∑ p : Fin d × Fin d, ((a p.1 p.2).bound*K+(da p.1 p.2).bound*M) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro p _ _
        exact add_nonneg (mul_nonneg (a _ _).bound_nonneg hK) (mul_nonneg (da _ _).bound_nonneg hM)
      _ = _ := Fintype.sum_prod_type _
  obtain ⟨w,hw,hn⟩ := weak_derivative_divide_coefficient hS (a r r) (da r r) (ha r r) _
    (hda r r) hκ hpos (G r) R hR
  refine ⟨w,hw,hn.trans (add_le_add (mul_le_mul_of_nonneg_left hRn (by positivity)) ?_)⟩
  exact mul_le_mul_of_nonneg_left (hG r)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (da r r).bound_nonneg) (a r r).bound_nonneg)

theorem exists_variable_H2_of_tangential_test_bounds (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (a da : Fin d → Fin d → BoundedMultiplier (volume.restrict S))
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j).value S)
    (hda : ∀ i j, (da i j).value =ᵐ[volume.restrict S]
      fun x => fderiv ℝ (a i j).value x (EuclideanSpace.basisFun (Fin d) ℝ j))
    (r : Fin d) {κ : ℝ} (hκ : 0 < κ) (hpos : ∀ x ∈ S, κ ≤ |(a r r).value x|)
    (f : Lp ℝ 2 (volume.restrict S))
    (hf : ∀ φ : SpatialTest S,
      (∑ i, ∑ j, inner ℝ ((a i j).map
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)))
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)))=
      inner ℝ f (φ.toLp (volume.restrict S)))
    {K : ℝ} (hK : 0 ≤ K)
    (ht : ∀ i j, j ≠ r → ∀ φ : SpatialTest S,
      |inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j))| ≤
      K*‖φ.toLp (volume.restrict S)‖) :
    let M := ‖WeakSobolevJet.field 1 u‖
    let N := κ⁻¹*(‖f‖+∑ i, ∑ j, ((a i j).bound*K+(da i j).bound*M))+
      (κ⁻¹)^2*(da r r).bound*(a r r).bound*M
    ∃ U : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u ∧
      ‖WeakSobolevJet.field 2 U‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*(max K N)^2 := by
  classical
  let G i := derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)
  have ht' (i j : Fin d) (hij : (i,j) ≠ (r,r)) (φ : SpatialTest S) :
      |inner ℝ (G i) (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j))| ≤
        K*‖φ.toLp (volume.restrict S)‖ := by
    by_cases hj : j=r
    · subst j
      have hi : i ≠ r := fun hi => hij (by rw [hi])
      change |inner ℝ (derivativeComponent _ _) _| ≤ _
      rw [weakGradient_test_mixed_commute u i r φ]
      exact ht r i hi φ
    · exact ht i j hj φ
  have he (i j : Fin d) : ∃ v : Lp ℝ 2 (volume.restrict S), (i,j) ≠ (r,r) →
      ‖v‖ ≤ K ∧ IsWeakSpatialDerivative (volume.restrict S) S
        (EuclideanSpace.basisFun (Fin d) ℝ j) (G i) v := by
    by_cases hij : (i,j) ≠ (r,r)
    · obtain ⟨v,hv,hd⟩ := exists_weakSpatialDerivative_of_test_bound hS (G i) j hK (ht' i j hij)
      exact ⟨v,fun _ => ⟨hv,hd⟩⟩
    · exact ⟨0,fun hij' => (hij hij').elim⟩
  choose D hD using he
  obtain ⟨w,hw,hn⟩ := exists_normal_derivative_of_matrix_equation hS a da ha hda r hκ hpos G f D
    (fun i j hij => (hD i j hij).2) (norm_nonneg _) hK
    (fun i => derivativeComponent_norm_le _ _) (fun i j hij => (hD i j hij).1) hf
  dsimp only
  apply exists_weakH2_of_gradient_test_bounds hS u (le_max_of_le_left hK)
  intro i j φ
  by_cases hij : (i,j)=(r,r)
  · have hi := congrArg Prod.fst hij
    have hj := congrArg Prod.snd hij
    dsimp only at hi hj
    subst i; subst j
    change |inner ℝ (G r) _| ≤ _
    rw [hw φ,abs_neg]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (hn.trans (le_max_right _ _)) (norm_nonneg _))
  · exact (ht' i j hij φ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

theorem matrixGradientPairing_test_restricted (hS : IsOpen S)
    (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (φ : SpatialTest S) :
    matrixGradientPairing a (WeakSobolevJet.zeroExtendDirichlet hS u hu) φ.fullJet =
      ∑ i, ∑ j, inner ℝ (((a i j).restrictMeasure Measure.restrict_le_self).map
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)))
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)) := by
  rw [matrixGradientPairing_test_integral]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((a i j).restrictMeasure (ν := volume.restrict S) Measure.restrict_le_self).map_ae
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)),
    φ.derivativeLp_ae (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)] with x hx hd
  rw [hx,hd]
  simp only [RCLike.inner_apply,conj_trivial,smul_eq_mul,BoundedMultiplier.restrictMeasure]
  ring

theorem exists_variable_dirichlet_H2_of_tangential_invariance (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j).value S)
    {C : Fin d → Fin d → NNReal} (hC : ∀ i j, LipschitzWith (C i j) (a i j).value)
    {κ : ℝ} (hκ : 0 < κ)
    (hA : ∀ᵐ x ∂volume, ∀ ξ : Fin d → ℝ,
      κ*(∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, (a i j).value x*(ξ i)*(ξ j))
    (f : Lp ℝ 2 (volume.restrict S))
    (hf : ∀ φ : SpatialTest S, matrixGradientPairing a
      (WeakSobolevJet.zeroExtendDirichlet hS u hu) φ.fullJet=inner ℝ f (φ.toLp (volume.restrict S)))
    (r : Fin d)
    (hSS : ∀ j : Fin d, j ≠ r → ∀ t : ℝ,
      (fun x => x+t • EuclideanSpace.basisFun (Fin d) ℝ j) ⁻¹' S ⊆ S) :
    let M := ‖WeakSobolevJet.field 1 u‖
    let K := κ⁻¹*(‖f‖+(∑ i, ∑ j, (C i j : ℝ))*M)
    let N := κ⁻¹*(‖f‖+∑ i, ∑ j, ((a i j).bound*K+(C i j : ℝ)*M))+
      (κ⁻¹)^2*(C r r : ℝ)*(a r r).bound*M
    ∃ U : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u ∧
      ‖WeakSobolevJet.field 2 U‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*(max K N)^2 := by
  let b i j := (a i j).restrictMeasure (ν := volume.restrict S) Measure.restrict_le_self
  let db i j := (a i j).spatialDerivativeOn hS (ha i j) (hC i j) j
  have hpos (x) (_hx : x ∈ S) : κ ≤ |(b r r).value x| :=
    (matrix_elliptic_diagonal a hC κ hA r x).trans (le_abs_self _)
  have heq (φ : SpatialTest S) :
      (∑ i, ∑ j, inner ℝ ((b i j).map
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)))
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)))=
        inner ℝ f (φ.toLp (volume.restrict S)) := by
    rw [← matrixGradientPairing_test_restricted hS a u hu]
    exact hf φ
  exact exists_variable_H2_of_tangential_test_bounds hS u b db ha
    (fun _ _ => Eventually.of_forall fun _ => rfl) r hκ hpos f heq (by positivity)
    (fun i j hj φ => dirichlet_variable_tangential_test_bound hS u hu a hC hκ hA f hf j (hSS j hj) i φ)

theorem exists_variable_halfspace_dirichlet_H2 (r : Fin d) (c : ℝ)
    (u : WeakSobolevJet d 1 (volume.restrict {x : SpatialCoordinates d | c < x r}) {x | c < x r})
    (hu : u ∈ dirichletJetSpace {x : SpatialCoordinates d | c < x r})
    (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j).value {x | c < x r})
    {C : Fin d → Fin d → NNReal} (hC : ∀ i j, LipschitzWith (C i j) (a i j).value)
    {κ : ℝ} (hκ : 0 < κ)
    (hA : ∀ᵐ x ∂volume, ∀ ξ : Fin d → ℝ,
      κ*(∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, (a i j).value x*(ξ i)*(ξ j))
    (f : Lp ℝ 2 (volume.restrict {x : SpatialCoordinates d | c < x r}))
    (hf : ∀ φ : SpatialTest {x : SpatialCoordinates d | c < x r},
      (∑ i, ∑ j, ∫ x in {x : SpatialCoordinates d | c < x r},
        (a i j).value x*(derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) x)*
          (fderiv ℝ φ.value x (EuclideanSpace.basisFun (Fin d) ℝ j)))=
      inner ℝ f (φ.toLp (volume.restrict {x : SpatialCoordinates d | c < x r}))) :
    let M := ‖WeakSobolevJet.field 1 u‖
    let K := κ⁻¹*(‖f‖+(∑ i, ∑ j, (C i j : ℝ))*M)
    let N := κ⁻¹*(‖f‖+∑ i, ∑ j, ((a i j).bound*K+(C i j : ℝ)*M))+
      (κ⁻¹)^2*(C r r : ℝ)*(a r r).bound*M
    ∃ U : WeakSobolevJet d 2 (volume.restrict {x : SpatialCoordinates d | c < x r}) {x | c < x r},
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u ∧
      ‖WeakSobolevJet.field 2 U‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*(max K N)^2 := by
  have hopen : IsOpen {x : SpatialCoordinates d | c < x r} :=
    isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r)
  have hSS : ∀ j : Fin d, j ≠ r → ∀ t : ℝ,
      (fun x => x+t • EuclideanSpace.basisFun (Fin d) ℝ j) ⁻¹' {x : SpatialCoordinates d | c < x r} ⊆
        {x | c < x r} := by
    intro j hj t x hx
    have hcoord : (x+t • EuclideanSpace.basisFun (Fin d) ℝ j) r=x r := by
      simp [EuclideanSpace.basisFun_apply,PiLp.add_apply,PiLp.smul_apply,Ne.symm hj]
    change c < (x+t • EuclideanSpace.basisFun (Fin d) ℝ j) r at hx
    change c < x r
    simpa only [hcoord] using hx
  apply exists_variable_dirichlet_H2_of_tangential_invariance hopen u hu a ha hC hκ hA f _ r hSS
  intro φ
  rw [matrixGradientPairing_test_integral]
  exact hf φ

end Carleman
