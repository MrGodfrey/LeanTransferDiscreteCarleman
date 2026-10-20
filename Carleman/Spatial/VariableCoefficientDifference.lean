module
public import Carleman.Spatial.DirichletDifferenceQuotient
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {d : ℕ}
namespace BoundedMultiplier

def spatialTranslate (a : BoundedMultiplier (volume : Measure (SpatialCoordinates d))) (z : SpatialCoordinates d) :
    BoundedMultiplier (volume : Measure (SpatialCoordinates d)) where
  value x := a.value (x+z)
  measurable := a.measurable.comp_quasiMeasurePreserving (measurePreserving_add_right volume z).quasiMeasurePreserving
  bound := a.bound
  bound_nonneg := a.bound_nonneg
  bounded := (measurePreserving_add_right volume z).quasiMeasurePreserving.ae a.bounded

theorem spatialTranslate_map (a : BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    (z : SpatialCoordinates d) (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    spatialTranslationLp z (a.map u)=(a.spatialTranslate z).map (spatialTranslationLp z u) := by
  apply Lp.ext
  filter_upwards [spatialTranslationLp_ae z (a.map u),(a.spatialTranslate z).map_ae (spatialTranslationLp z u),
    spatialTranslationLp_ae z u,(measurePreserving_add_right volume z).quasiMeasurePreserving.ae (a.map_ae u)]
    with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  rfl

theorem lipschitz_difference_bound {a : SpatialCoordinates d → ℝ} {C : NNReal}
    (ha : LipschitzWith C a) (z : SpatialCoordinates d) (h : ℝ) (x : SpatialCoordinates d) :
    |h⁻¹*(a (x+h • z)-a x)| ≤ (C : ℝ)*‖z‖ := by
  by_cases hh : h=0
  · subst h
    simp only [inv_zero,zero_mul,abs_zero]
    positivity
  have hb := ha.norm_sub_le (x+h • z) x
  rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at hb
  rw [abs_mul,abs_inv]
  calc
    _ ≤ |h|⁻¹*((C : ℝ)*(|h| *‖z‖)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (C : ℝ)*‖z‖ := by field_simp

def spatialDifference (a : BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    {C : NNReal} (ha : LipschitzWith C a.value) (z : SpatialCoordinates d) (h : ℝ) :
    BoundedMultiplier (volume : Measure (SpatialCoordinates d)) where
  value x := h⁻¹*(a.value (x+h • z)-a.value x)
  measurable := ((a.spatialTranslate (h • z)).measurable.sub a.measurable).const_mul h⁻¹
  bound := (C : ℝ)*‖z‖
  bound_nonneg := by positivity
  bounded := Eventually.of_forall (lipschitz_difference_bound ha z h)

theorem differenceQuotient_product (a : BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    {C : NNReal} (ha : LipschitzWith C a.value) (z : SpatialCoordinates d) (h : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    spatialDifferenceQuotient z h (a.map u)=
      (a.spatialTranslate (h • z)).map (spatialDifferenceQuotient z h u)+(a.spatialDifference ha z h).map u := by
  apply Lp.ext
  filter_upwards [spatialDifferenceQuotient_ae z h (a.map_ae u),
    spatialDifferenceQuotient_ae z h (u := u) (Eventually.of_forall fun _ => rfl),
    (a.spatialTranslate (h • z)).map_ae (spatialDifferenceQuotient z h u),
    (a.spatialDifference ha z h).map_ae u,
    Lp.coeFn_add ((a.spatialTranslate (h • z)).map (spatialDifferenceQuotient z h u))
      ((a.spatialDifference ha z h).map u)] with x h1 h2 h3 h4 h5
  rw [h1,h5]
  simp only [Pi.add_apply]
  rw [h3,h4,h2]
  change h⁻¹*(a.value (x+h • z)*u (x+h • z)-a.value x*u x)=
    a.value (x+h • z)*(h⁻¹*(u (x+h • z)-u x))+(h⁻¹*(a.value (x+h • z)-a.value x))*u x
  ring

theorem differenceQuotient_commutator_bound (a : BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    {C : NNReal} (ha : LipschitzWith C a.value) (z : SpatialCoordinates d) (h : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    ‖spatialDifferenceQuotient z h (a.map u)-
      (a.spatialTranslate (h • z)).map (spatialDifferenceQuotient z h u)‖ ≤ (C : ℝ)*‖z‖*‖u‖ := by
  rw [differenceQuotient_product a ha,add_sub_cancel_left]
  exact (a.spatialDifference ha z h).seminorm_le u

end BoundedMultiplier


def matrixL2Pairing {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (a : Fin d → Fin d → BoundedMultiplier ν) (G H : Fin d → Lp ℝ 2 ν) : ℝ :=
  ∑ i, ∑ j, inner ℝ ((a i j).map (G i)) (H j)

theorem matrixL2Pairing_bound {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (a : Fin d → Fin d → BoundedMultiplier ν) (G H : Fin d → Lp ℝ 2 ν)
    {M N : ℝ} (hM : 0 ≤ M) (hG : ∀ i, ‖G i‖ ≤ M) (hH : ∀ j, ‖H j‖ ≤ N) :
    |matrixL2Pairing a G H| ≤ (∑ i, ∑ j, (a i j).bound)*M*N := by
  have hb (i j : Fin d) : |inner ℝ ((a i j).map (G i)) (H j)| ≤ (a i j).bound*M*N := by
    apply (abs_real_inner_le_norm _ _).trans
    exact mul_le_mul ((a i j).seminorm_le (G i) |>.trans
      (mul_le_mul_of_nonneg_left (hG i) (a i j).bound_nonneg)) (hH j) (norm_nonneg _) (mul_nonneg (a i j).bound_nonneg hM)
  calc
    _ ≤ ∑ i, |∑ j, inner ℝ ((a i j).map (G i)) (H j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |inner ℝ ((a i j).map (G i)) (H j)| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (a i j).bound*M*N := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = _ := by simp only [Finset.sum_mul]

theorem matrixL2Pairing_coercive {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (a : Fin d → Fin d → BoundedMultiplier ν) (G : Fin d → Lp ℝ 2 ν) (κ : ℝ)
    (hA : ∀ᵐ x ∂ν, ∀ ξ : Fin d → ℝ,
      κ*(∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, (a i j).value x*(ξ i)*(ξ j)) :
    κ*(∑ i, ‖G i‖^2) ≤ matrixL2Pairing a G G := by
  let F (x : Ω) := ∑ i, ∑ j, inner ℝ ((a i j).map (G i) x) (G j x)
  have hF : Integrable F ν := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => L2.integrable_inner _ _
  have hL : Integrable (fun x => κ*(∑ i, (G i x)^2)) ν :=
    (integrable_finsetSum _ fun i _ => (Lp.memLp (G i)).integrable_sq).const_mul κ
  have hright : (∫ x, F x ∂ν)=matrixL2Pairing a G G := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => L2.integrable_inner _ _)]
    unfold matrixL2Pairing
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => L2.integrable_inner ((a i j).map (G i)) (G j))]
    simp only [L2.inner_def]
  have hleft : (∫ x, κ*(∑ i, (G i x)^2) ∂ν)=κ*(∑ i, ‖G i‖^2) := by
    rw [integral_const_mul,integral_finsetSum _ (fun i _ => (Lp.memLp (G i)).integrable_sq)]
    simp only [integral_sq_eq_bochnerL2Norm_sq (Lp.memLp _),bochnerL2Norm_coe]
  rw [← hleft,← hright]
  apply integral_mono_ae hL hF
  filter_upwards [hA,ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => (a i j).map_ae (G i)))] with x hx ha
  have hid : F x=∑ i, ∑ j, (a i j).value x*(G i x)*(G j x) := by
    dsimp only [F]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha i j]
    simp only [smul_eq_mul,RCLike.inner_apply,conj_trivial]
    ring
  rw [hid]
  exact hx (fun i => G i x)


def matrixGradientPairing {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    {S : Set (SpatialCoordinates d)} (a : Fin d → Fin d → BoundedMultiplier ν)
    (u v : WeakSobolevJet d 1 ν S) : ℝ :=
  matrixL2Pairing a
    (fun i => derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
    (fun j => derivativeComponent (Sym.cons j Sym.nil) (WeakSobolevJet.field 1 v))

theorem matrixGradientPairing_coercive {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    {S : Set (SpatialCoordinates d)} (a : Fin d → Fin d → BoundedMultiplier ν)
    (u : WeakSobolevJet d 1 ν S) (κ : ℝ)
    (hA : ∀ᵐ x ∂ν, ∀ ξ : Fin d → ℝ,
      κ*(∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, (a i j).value x*(ξ i)*(ξ j)) :
    κ*‖WeakSobolevJet.field 1 u‖^2 ≤ matrixGradientPairing a u u := by
  have he := firstDerivativeField_inner (WeakSobolevJet.field 1 u) (WeakSobolevJet.field 1 u)
  simp only [real_inner_self_eq_norm_sq] at he
  rw [he]
  exact matrixL2Pairing_coercive a _ κ hA

theorem matrixGradientPairing_bound {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    {S : Set (SpatialCoordinates d)} (a : Fin d → Fin d → BoundedMultiplier ν)
    (u v : WeakSobolevJet d 1 ν S) :
    |matrixGradientPairing a u v| ≤ (∑ i, ∑ j, (a i j).bound)*
      ‖WeakSobolevJet.field 1 u‖*‖WeakSobolevJet.field 1 v‖ :=
  matrixL2Pairing_bound a _ _ (norm_nonneg _) (fun _i => derivativeComponent_norm_le _ _)
    (fun _j => derivativeComponent_norm_le _ _)

theorem matrixGradientPairing_difference (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    {C : Fin d → Fin d → NNReal} (hC : ∀ i j, LipschitzWith (C i j) (a i j).value)
    (z : SpatialCoordinates d) (h : ℝ) (u v : WeakSobolevJet d 1 volume univ) :
    -matrixGradientPairing a u (WeakSobolevJet.differenceFirst z (-h) v)=
      matrixGradientPairing (fun i j => (a i j).spatialTranslate (h • z)) (WeakSobolevJet.differenceFirst z h u) v+
      matrixGradientPairing (fun i j => (a i j).spatialDifference (hC i j) z h) u v := by
  simp only [matrixGradientPairing,matrixL2Pairing,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [WeakSobolevJet.differenceFirst_gradient,WeakSobolevJet.differenceFirst_gradient,
    ← spatialDifferenceQuotient_inner,BoundedMultiplier.differenceQuotient_product (a i j) (hC i j),inner_add_left]

theorem matrixGradientPairing_tendsto_right {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    {S : Set (SpatialCoordinates d)} (a : Fin d → Fin d → BoundedMultiplier ν)
    (u : WeakSobolevJet d 1 ν S) {V : ℕ → WeakSobolevJet d 1 ν S} {v : WeakSobolevJet d 1 ν S}
    (ht : Tendsto V atTop (𝓝 v)) :
    Tendsto (fun n => matrixGradientPairing a u (V n)) atTop (𝓝 (matrixGradientPairing a u v)) := by
  simp only [matrixGradientPairing,matrixL2Pairing]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (tendsto_const_nhds (x := (a i j).map
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)))).inner (𝕜 := ℝ)
    (((derivativeComponentCLM (Sym.cons j Sym.nil)).continuous.tendsto _).comp
      ((WeakSobolevJet.fieldCLM 1).continuous.tendsto v |>.comp ht))

theorem matrixGradient_equation_dirichlet {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    (U : WeakSobolevJet d 1 volume univ) (f : Lp ℝ 2 (volume.restrict S))
    (hf : ∀ φ : SpatialTest S, matrixGradientPairing a U φ.fullJet=inner ℝ f (φ.toLp (volume.restrict S)))
    (v : WeakSobolevJet d 1 (volume.restrict S) S) (hv : v ∈ dirichletJetSpace S) :
    matrixGradientPairing a U (WeakSobolevJet.zeroExtendDirichlet hS v hv)=inner ℝ f (WeakSobolevJet.value v) := by
  obtain ⟨V,hV,ht⟩ := mem_closure_iff_seq_limit.mp hv
  choose φ hφ using fun n => exists_test_of_mem_test_span hS (hV n)
  have hv' (n : ℕ) : V n ∈ dirichletJetSpace S := Submodule.le_topologicalClosure _ (hV n)
  have hl := matrixGradientPairing_tendsto_right a U (WeakSobolevJet.zeroExtendDirichlet_tendsto hS V hv' v hv ht)
  have hr := (tendsto_const_nhds (x := f)).inner (𝕜 := ℝ) (WeakSobolevJet.valueCLM.continuous.tendsto v |>.comp ht)
  apply tendsto_nhds_unique hl
  apply hr.congr'
  exact Eventually.of_forall fun n => by
    change inner ℝ f (WeakSobolevJet.value (V n))=
      matrixGradientPairing a U (WeakSobolevJet.zeroExtendDirichlet hS (V n) (hv' n))
    simp only [← hφ n,← SpatialTest.fullJet_eq_zeroExtend hS,SpatialTest.sobolevJet_value]
    exact (hf (φ n)).symm


theorem dirichlet_variable_tangential_difference_gradient_bound {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    {C : Fin d → Fin d → NNReal} (hC : ∀ i j, LipschitzWith (C i j) (a i j).value)
    {κ : ℝ} (hκ : 0 < κ)
    (hA : ∀ᵐ x ∂volume, ∀ ξ : Fin d → ℝ,
      κ*(∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, (a i j).value x*(ξ i)*(ξ j))
    (f : Lp ℝ 2 (volume.restrict S))
    (hf : ∀ φ : SpatialTest S, matrixGradientPairing a
      (WeakSobolevJet.zeroExtendDirichlet hS u hu) φ.fullJet=inner ℝ f (φ.toLp (volume.restrict S)))
    (i : Fin d) (h : ℝ)
    (hp : (fun x => x+h • EuclideanSpace.basisFun (Fin d) ℝ i) ⁻¹' S ⊆ S)
    (hm : (fun x => x+(-h) • EuclideanSpace.basisFun (Fin d) ℝ i) ⁻¹' S ⊆ S) :
    ‖WeakSobolevJet.field 1 (WeakSobolevJet.differenceFirst (EuclideanSpace.basisFun (Fin d) ℝ i) h
      (WeakSobolevJet.zeroExtendDirichlet hS u hu))‖ ≤
        κ⁻¹*(‖f‖+(∑ i, ∑ j, (C i j : ℝ))*‖WeakSobolevJet.field 1 u‖) := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ i
  let U := WeakSobolevJet.zeroExtendDirichlet hS u hu
  let W := WeakSobolevJet.differenceFirst e h U
  let w := WeakSobolevJet.restrictDomain S W
  have hw : w ∈ dirichletJetSpace S := WeakSobolevJet.differenceFirst_dirichlet_mem hS u hu e h hp
  have hW : WeakSobolevJet.zeroExtendDirichlet hS w hw=W :=
    WeakSobolevJet.differenceFirst_dirichlet_extension hS u hu e h hp
  let Q := WeakSobolevJet.differenceFirst e (-h) W
  let q := WeakSobolevJet.restrictDomain S Q
  have hq : q ∈ dirichletJetSpace S := by
    have ht := WeakSobolevJet.differenceFirst_dirichlet_mem hS w hw e (-h) hm
    simp only [hW] at ht
    exact ht
  have hQ : WeakSobolevJet.zeroExtendDirichlet hS q hq=Q := by
    have ht := WeakSobolevJet.differenceFirst_dirichlet_extension hS w hw e (-h) hm
    simp only [hW] at ht
    exact ht
  have he := matrixGradient_equation_dirichlet hS a U f hf q hq
  rw [hQ] at he
  have hen : ‖e‖=1 := (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one i
  have hUn : ‖WeakSobolevJet.field 1 U‖=‖WeakSobolevJet.field 1 u‖ :=
    WeakSobolevJet.zeroExtendDirichlet_field_norm hS u hu 1
  have hco := matrixGradientPairing_coercive (fun i j => (a i j).spatialTranslate (h • e)) W κ
    ((measurePreserving_add_right volume (h • e)).quasiMeasurePreserving.ae hA)
  have hi := matrixGradientPairing_difference a hC e h U W
  change -matrixGradientPairing a U Q=matrixGradientPairing (fun i j => (a i j).spatialTranslate (h • e)) W W+
    matrixGradientPairing (fun i j => (a i j).spatialDifference (hC i j) e h) U W at hi
  rw [he] at hi
  have hn : ‖WeakSobolevJet.value q‖ ≤ ‖WeakSobolevJet.field 1 W‖ := by
    rw [WeakSobolevJet.restrictDomain_value]
    apply (Physical.restrictRegionLp_norm_le S _).trans
    rw [WeakSobolevJet.differenceFirst_value]
    exact ((W.property 0 Sym.nil i).differenceQuotient_bound (-h)).trans (derivativeComponent_norm_le _ _)
  have hload := (neg_le_abs (inner ℝ f (WeakSobolevJet.value q))).trans
    ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg f)))
  have herr := matrixGradientPairing_bound (fun i j => (a i j).spatialDifference (hC i j) e h) U W
  change |matrixGradientPairing (fun i j => (a i j).spatialDifference (hC i j) e h) U W| ≤
    (∑ i, ∑ j, (C i j : ℝ)*‖e‖)*‖WeakSobolevJet.field 1 U‖*‖WeakSobolevJet.field 1 W‖ at herr
  simp only [hen,mul_one,hUn] at herr
  have herr' := (neg_le_abs (matrixGradientPairing (fun i j => (a i j).spatialDifference (hC i j) e h) U W)).trans herr
  change ‖WeakSobolevJet.field 1 W‖ ≤ _
  rw [inv_mul_eq_div,le_div_iff₀ hκ]
  by_cases hz : ‖WeakSobolevJet.field 1 W‖=0
  · rw [hz,zero_mul]
    positivity
  · have hpos := lt_of_le_of_ne (norm_nonneg (WeakSobolevJet.field 1 W)) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith


theorem matrixGradientPairing_dirichlet_integral {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    (u v : WeakSobolevJet d 1 (volume.restrict S) S)
    (hu : u ∈ dirichletJetSpace S) (hv : v ∈ dirichletJetSpace S) :
    matrixGradientPairing a (WeakSobolevJet.zeroExtendDirichlet hS u hu)
      (WeakSobolevJet.zeroExtendDirichlet hS v hv)=
    ∑ i, ∑ j, ∫ x in S, (a i j).value x*
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) x)*
      (derivativeComponent (Sym.cons j Sym.nil) (WeakSobolevJet.field 1 v) x) := by
  unfold matrixGradientPairing matrixL2Pairing
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let g := derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)
  let k := derivativeComponent (Sym.cons j Sym.nil) (WeakSobolevJet.field 1 v)
  change inner ℝ ((a i j).map (derivativeComponent (Sym.cons i Sym.nil)
    (zeroExtendLp hS.measurableSet (WeakSobolevJet.field 1 u))))
      (derivativeComponent (Sym.cons j Sym.nil) (zeroExtendLp hS.measurableSet (WeakSobolevJet.field 1 v)))=_
  rw [derivativeComponent_zeroExtend,derivativeComponent_zeroExtend,L2.inner_def]
  calc
    _ = ∫ x, ((a i j).value x*zeroExtendLp hS.measurableSet g x)*zeroExtendLp hS.measurableSet k x := by
      apply integral_congr_ae
      filter_upwards [(a i j).map_ae (zeroExtendLp hS.measurableSet g)] with x hx
      rw [hx]
      simp only [smul_eq_mul,RCLike.inner_apply,conj_trivial]
      ring
    _ = ∫ x in S, ((a i j).value x*zeroExtendLp hS.measurableSet g x)*k x :=
      integral_mul_zeroExtendLp hS.measurableSet k _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [zeroExtendLp_ae_restrict hS.measurableSet g] with x hx
      rw [hx]

theorem matrixGradientPairing_test_integral {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S) (φ : SpatialTest S) :
    matrixGradientPairing a (WeakSobolevJet.zeroExtendDirichlet hS u hu) φ.fullJet=
      ∑ i, ∑ j, ∫ x in S, (a i j).value x*
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) x)*
        (fderiv ℝ φ.value x (EuclideanSpace.basisFun (Fin d) ℝ j)) := by
  rw [φ.fullJet_eq_zeroExtend hS,matrixGradientPairing_dirichlet_integral]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [φ.sobolevJet_derivative]
  apply integral_congr_ae
  filter_upwards [φ.derivativeLp_ae (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j)] with x hx
  rw [hx]

theorem dirichlet_variable_tangential_test_bound {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (a : Fin d → Fin d → BoundedMultiplier (volume : Measure (SpatialCoordinates d)))
    {C : Fin d → Fin d → NNReal} (hC : ∀ i j, LipschitzWith (C i j) (a i j).value)
    {κ : ℝ} (hκ : 0 < κ)
    (hA : ∀ᵐ x ∂volume, ∀ ξ : Fin d → ℝ,
      κ*(∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, (a i j).value x*(ξ i)*(ξ j))
    (f : Lp ℝ 2 (volume.restrict S))
    (hf : ∀ φ : SpatialTest S, matrixGradientPairing a
      (WeakSobolevJet.zeroExtendDirichlet hS u hu) φ.fullJet=inner ℝ f (φ.toLp (volume.restrict S)))
    (j : Fin d) (hSS : ∀ t : ℝ, (fun x => x+t • EuclideanSpace.basisFun (Fin d) ℝ j) ⁻¹' S ⊆ S)
    (i : Fin d) (φ : SpatialTest S) :
    |inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
      (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j))| ≤
      (κ⁻¹*(‖f‖+(∑ i, ∑ j, (C i j : ℝ))*‖WeakSobolevJet.field 1 u‖))*‖φ.toLp (volume.restrict S)‖ := by
  let U := WeakSobolevJet.zeroExtendDirichlet hS u hu
  let G := derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 U)
  have hG : Physical.restrictRegionLp S G=
      derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) := by
    rw [← derivativeComponent_restrict]
    change derivativeComponent (Sym.cons i Sym.nil)
      (WeakSobolevJet.field 1 (WeakSobolevJet.restrictDomain S U))=_
    rw [WeakSobolevJet.zeroExtendDirichlet_restrict]
  have hb (t : ℝ) : ‖Physical.restrictRegionLp S
      (spatialDifferenceQuotient (EuclideanSpace.basisFun (Fin d) ℝ j) t G)‖ ≤
        κ⁻¹*(‖f‖+(∑ i, ∑ j, (C i j : ℝ))*‖WeakSobolevJet.field 1 u‖) := by
    apply (Physical.restrictRegionLp_norm_le S _).trans
    rw [← WeakSobolevJet.differenceFirst_gradient]
    exact (derivativeComponent_norm_le _ _).trans
      (dirichlet_variable_tangential_difference_gradient_bound hS u hu a hC hκ hA f hf j t (hSS t) (hSS (-t)))
  rw [← hG]
  exact differenceQuotient_test_bound hS G _ (h := fun n : ℕ => 1/((n : ℝ)+1))
    (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun _ => hb _) φ

end Carleman
