module
public import Carleman.Spatial.DifferenceQuotientCriterion
public import Carleman.Spatial.FirstComponentJet
public import Carleman.Spatial.FullSpaceTestPairing
public import Carleman.Spatial.DirichletExtensionContinuity
public import Carleman.Spatial.WeakProductComponents
public import Carleman.Spatial.WeakLaplacianLimit
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {d : ℕ}

namespace WeakSobolevJet

def translateFirst (z : SpatialCoordinates d) (u : WeakSobolevJet d 1 volume univ) :
    WeakSobolevJet d 1 volume univ :=
  firstComponentJet (spatialTranslationLp z (value u))
    (fun i => spatialTranslationLp z (derivativeComponent (Sym.cons i Sym.nil) (field 1 u)))
    (fun i => (u.property 0 Sym.nil i).translation z)

theorem translateFirst_value (z : SpatialCoordinates d) (u : WeakSobolevJet d 1 volume univ) :
    value (translateFirst z u)=spatialTranslationLp z (value u) := firstComponentJet_value _ _ _

theorem translateFirst_gradient (z : SpatialCoordinates d) (u : WeakSobolevJet d 1 volume univ) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (field 1 (translateFirst z u))=
      spatialTranslationLp z (derivativeComponent (Sym.cons i Sym.nil) (field 1 u)) :=
  firstComponentJet_gradient _ _ _ i

theorem translateFirst_tendsto (z : SpatialCoordinates d)
    {U : ℕ → WeakSobolevJet d 1 volume univ} {u : WeakSobolevJet d 1 volume univ}
    (ht : Tendsto U atTop (𝓝 u)) :
    Tendsto (fun n => translateFirst z (U n)) atTop (𝓝 (translateFirst z u)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro k
  fin_cases k
  · change Tendsto (fun n => (OperatorMultiplier.const scalarZeroFiber).continuousLinearMap
      (spatialTranslationLp z (value (U n)))) atTop
      (𝓝 ((OperatorMultiplier.const scalarZeroFiber).continuousLinearMap (spatialTranslationLp z (value u))))
    exact ((OperatorMultiplier.const scalarZeroFiber).continuousLinearMap.continuous.tendsto _).comp
      (((spatialTranslationLp z).continuous.tendsto _).comp (valueCLM.continuous.tendsto u |>.comp ht))
  · change Tendsto (fun n => firstGradientAssembly (fun i => spatialTranslationLp z
      (derivativeComponent (Sym.cons i Sym.nil) (field 1 (U n))))) atTop
      (𝓝 (firstGradientAssembly (fun i => spatialTranslationLp z
        (derivativeComponent (Sym.cons i Sym.nil) (field 1 u)))))
    apply (firstGradientAssembly.continuous.tendsto _).comp
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((spatialTranslationLp z).continuous.tendsto _).comp
      (((derivativeComponentCLM (Sym.cons i Sym.nil)).continuous.tendsto _).comp
        ((fieldCLM 1).continuous.tendsto u |>.comp ht))

def differenceFirst (z : SpatialCoordinates d) (h : ℝ) (u : WeakSobolevJet d 1 volume univ) :
    WeakSobolevJet d 1 volume univ := h⁻¹ • (translateFirst (h • z) u-u)

theorem differenceFirst_value (z : SpatialCoordinates d) (h : ℝ) (u : WeakSobolevJet d 1 volume univ) :
    value (differenceFirst z h u)=spatialDifferenceQuotient z h (value u) := by
  simp only [differenceFirst,map_smul,map_sub,translateFirst_value,spatialDifferenceQuotient_apply]

theorem differenceFirst_gradient (z : SpatialCoordinates d) (h : ℝ)
    (u : WeakSobolevJet d 1 volume univ) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (field 1 (differenceFirst z h u))=
      spatialDifferenceQuotient z h (derivativeComponent (Sym.cons i Sym.nil) (field 1 u)) := by
  simp only [differenceFirst,map_smul,map_sub,translateFirst_gradient,spatialDifferenceQuotient_apply]

theorem differenceFirst_gradient_pairing (z : SpatialCoordinates d) (h : ℝ)
    (u v : WeakSobolevJet d 1 volume univ) :
    weakGradientPairing (differenceFirst z h u) v = -weakGradientPairing u (differenceFirst z (-h) v) := by
  rw [weakGradientPairing_coordinates,weakGradientPairing_coordinates,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [differenceFirst_gradient,differenceFirst_gradient,spatialDifferenceQuotient_inner]

theorem differenceFirst_energy (z : SpatialCoordinates d) (h : ℝ)
    (u : WeakSobolevJet d 1 volume univ) :
    weakGradientPairing u (-differenceFirst z (-h) (differenceFirst z h u))=
      ‖field 1 (differenceFirst z h u)‖^2 := by
  have hi := differenceFirst_gradient_pairing z h u (differenceFirst z h u)
  rw [weakGradientPairing_apply,real_inner_self_eq_norm_sq] at hi
  rw [weakGradientPairing_apply,map_neg,inner_neg_right]
  exact hi.symm

end WeakSobolevJet


def SpatialTest.translateInto {S T : Set (SpatialCoordinates d)}
    (φ : SpatialTest S) (z : SpatialCoordinates d) (hST : (fun x => x+z) ⁻¹' S ⊆ T) : SpatialTest T :=
  φ.pullbackAffine (ContinuousLinearEquiv.refl ℝ (SpatialCoordinates d)) z hST

theorem SpatialTest.translateFirst_test {S T : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hT : IsOpen T) (φ : SpatialTest S)
    (z : SpatialCoordinates d) (hST : (fun x => x+z) ⁻¹' S ⊆ T) :
    WeakSobolevJet.restrictDomain T (WeakSobolevJet.translateFirst z
      (WeakSobolevJet.zeroExtendDirichlet hS φ.sobolevJet (test_mem_dirichletJetSpace S φ)))=
        (φ.translateInto z hST).sobolevJet := by
  apply restrictedJet_eq_test hT
  rw [WeakSobolevJet.translateFirst_value]
  have hs := (measurePreserving_add_right volume z).quasiMeasurePreserving.ae_eq_comp
    (φ.zeroExtendDirichlet_value_ae hS)
  exact (spatialTranslationLp_ae z _).trans hs

theorem WeakSobolevJet.translateFirst_dirichlet_mem {S T : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (z : SpatialCoordinates d) (hST : (fun x => x+z) ⁻¹' S ⊆ T) :
    restrictDomain T (translateFirst z (zeroExtendDirichlet hS u hu)) ∈ dirichletJetSpace T := by
  obtain ⟨U,hU,ht⟩ := mem_closure_iff_seq_limit.mp hu
  choose φ hφ using fun n => exists_test_of_mem_test_span hS (hU n)
  have hu' (n : ℕ) : U n ∈ dirichletJetSpace S := Submodule.le_topologicalClosure _ (hU n)
  have he := restrictDomain_tendsto (S := T) (translateFirst_tendsto z
    (zeroExtendDirichlet_tendsto hS U hu' u hu ht))
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto he
  apply Eventually.of_forall
  intro n
  change restrictDomain T (translateFirst z (zeroExtendDirichlet hS (U n) (hu' n))) ∈ dirichletJetSpace T
  simp only [← hφ n,SpatialTest.translateFirst_test hS hT _ z hST]
  exact test_mem_dirichletJetSpace T _

theorem WeakSobolevJet.differenceFirst_dirichlet_mem {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (z : SpatialCoordinates d) (h : ℝ) (hSS : (fun x => x+h • z) ⁻¹' S ⊆ S) :
    restrictDomain S (differenceFirst z h (zeroExtendDirichlet hS u hu)) ∈ dirichletJetSpace S := by
  have ht := translateFirst_dirichlet_mem hS hS u hu (h • z) hSS
  have he : restrictDomain S (differenceFirst z h (zeroExtendDirichlet hS u hu))=
      h⁻¹ • (restrictDomain S (translateFirst (h • z) (zeroExtendDirichlet hS u hu))-u) := by
    apply value_injective hS (ae_restrict_mem hS.measurableSet)
    have hr := congrArg value (zeroExtendDirichlet_restrict hS u hu)
    simp only [restrictDomain_value] at hr
    have hclm (v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
        Physical.restrictRegionLp S v=Physical.restrictRegionCLM S v := rfl
    simp only [restrictDomain_value,differenceFirst_value,spatialDifferenceQuotient_apply,
      map_smul,map_sub,translateFirst_value,hclm] at hr ⊢
    rw [hr]
  rw [he]
  exact (dirichletJetSpace S).smul_mem h⁻¹ ((dirichletJetSpace S).sub_mem ht hu)


theorem WeakSobolevJet.zeroExtend_restrict_of_ae_zero {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (w : WeakSobolevJet d 1 volume univ)
    (hw : restrictDomain S w ∈ dirichletJetSpace S)
    (hz : ∀ᵐ x ∂volume, x ∉ S → value w x=0) :
    zeroExtendDirichlet hS (restrictDomain S w) hw=w := by
  apply value_injective isOpen_univ (Eventually.of_forall fun _ => mem_univ _)
  rw [zeroExtendDirichlet_value,restrictDomain_value]
  apply Lp.ext
  filter_upwards [zeroExtendLp_ae hS.measurableSet (Physical.restrictRegionLp S (value w)),
    (ae_restrict_iff' hS.measurableSet).mp (Physical.restrictRegionLp_ae S (value w)),hz]
    with x he hr hx
  rw [he]
  by_cases hxs : x ∈ S
  · rw [indicator_of_mem hxs,hr hxs]
  · rw [indicator_of_notMem hxs,hx hxs]

theorem WeakSobolevJet.differenceFirst_dirichlet_extension {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (z : SpatialCoordinates d) (h : ℝ) (hSS : (fun x => x+h • z) ⁻¹' S ⊆ S) :
    zeroExtendDirichlet hS (restrictDomain S (differenceFirst z h (zeroExtendDirichlet hS u hu)))
      (differenceFirst_dirichlet_mem hS u hu z h hSS)=differenceFirst z h (zeroExtendDirichlet hS u hu) := by
  apply zeroExtend_restrict_of_ae_zero hS
  rw [differenceFirst_value,zeroExtendDirichlet_value]
  filter_upwards [spatialDifferenceQuotient_ae z h (zeroExtendLp_ae hS.measurableSet (value u))]
    with x hx
  intro hxs
  have hxz : x+h • z ∉ S := fun hh => hxs (hSS hh)
  rw [hx,indicator_of_notMem hxs,indicator_of_notMem hxz,sub_self,mul_zero]


theorem dirichlet_tangential_difference_gradient_bound {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f)
    (i : Fin d) (h : ℝ)
    (hp : (fun x => x+h • EuclideanSpace.basisFun (Fin d) ℝ i) ⁻¹' S ⊆ S)
    (hm : (fun x => x+(-h) • EuclideanSpace.basisFun (Fin d) ℝ i) ⁻¹' S ⊆ S) :
    ‖WeakSobolevJet.field 1 (WeakSobolevJet.differenceFirst
      (EuclideanSpace.basisFun (Fin d) ℝ i) h (WeakSobolevJet.zeroExtendDirichlet hS u hu))‖ ≤ ‖f‖ := by
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
    rw [hW] at ht
    exact ht
  have he := (isWeakNegativeLaplacian_iff_dirichlet hS u f).mp hf (-q)
    ((dirichletJetSpace S).neg_mem hq)
  have hi : weakGradientPairing u (-q)=‖WeakSobolevJet.field 1 W‖^2 := by
    have he := WeakSobolevJet.differenceFirst_energy e h U
    change weakGradientPairing U (-Q)=_ at he
    rw [weakGradientPairing_apply,map_neg,inner_neg_right] at he ⊢
    change -weakGradientPairing u q=_
    rw [← WeakSobolevJet.zeroExtendDirichlet_pairing hS u hu Q]
    exact he
  rw [hi,map_neg,inner_neg_right] at he
  have hn : ‖WeakSobolevJet.value q‖ ≤ ‖WeakSobolevJet.field 1 W‖ := by
    rw [WeakSobolevJet.restrictDomain_value]
    apply (Physical.restrictRegionLp_norm_le S _).trans
    rw [WeakSobolevJet.differenceFirst_value]
    exact ((W.property 0 Sym.nil i).differenceQuotient_bound (-h)).trans
      (derivativeComponent_norm_le _ _)
  have hb := (neg_le_abs (inner ℝ f (WeakSobolevJet.value q))).trans
    ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg f)))
  rw [← he] at hb
  by_contra hbad
  have hpos : 0 < ‖WeakSobolevJet.field 1 W‖ := (norm_nonneg f).trans_lt (lt_of_not_ge hbad)
  have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge hbad) hpos
  nlinarith


theorem weakGradient_test_mixed_commute {S : Set (SpatialCoordinates d)}
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (i j : Fin d) (φ : SpatialTest S) :
    inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
      (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j))=
    inner ℝ (derivativeComponent (Sym.cons j Sym.nil) (WeakSobolevJet.field 1 u))
      (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  have hi := u.property 0 Sym.nil i (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ j))
  have hj := u.property 0 Sym.nil j (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i))
  rw [φ.derivativeTest_toLp] at hi hj
  rw [φ.derivativeTest_derivativeLp_commute] at hi
  exact neg_injective (hi.symm.trans hj)

theorem dirichlet_tangential_test_bound {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f)
    (j : Fin d) (hSS : ∀ t : ℝ, (fun x => x+t • EuclideanSpace.basisFun (Fin d) ℝ j) ⁻¹' S ⊆ S)
    (i : Fin d) (φ : SpatialTest S) :
    |inner ℝ (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
      (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j))| ≤
        ‖f‖*‖φ.toLp (volume.restrict S)‖ := by
  let U := WeakSobolevJet.zeroExtendDirichlet hS u hu
  let G := derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 U)
  have hG : Physical.restrictRegionLp S G=
      derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) := by
    rw [← derivativeComponent_restrict]
    change derivativeComponent (Sym.cons i Sym.nil)
      (WeakSobolevJet.field 1 (WeakSobolevJet.restrictDomain S U))=_
    rw [WeakSobolevJet.zeroExtendDirichlet_restrict]
  have hb (t : ℝ) : ‖Physical.restrictRegionLp S
      (spatialDifferenceQuotient (EuclideanSpace.basisFun (Fin d) ℝ j) t G)‖ ≤ ‖f‖ := by
    apply (Physical.restrictRegionLp_norm_le S _).trans
    rw [← WeakSobolevJet.differenceFirst_gradient]
    exact (derivativeComponent_norm_le _ _).trans
      (dirichlet_tangential_difference_gradient_bound hS u hu f hf j t (hSS t) (hSS (-t)))
  rw [← hG]
  exact differenceQuotient_test_bound hS G _ (h := fun n : ℕ => 1/((n : ℝ)+1))
    (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun n => hb _) φ

theorem exists_dirichlet_H2_of_tangential_invariance {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d)
    (hSS : ∀ j : Fin d, j ≠ r → ∀ t : ℝ,
      (fun x => x+t • EuclideanSpace.basisFun (Fin d) ℝ j) ⁻¹' S ⊆ S) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict S) S,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u ∧
      ‖WeakSobolevJet.field 2 U‖^2 ≤
        (Fintype.card (Sym (Fin d) 2) : ℝ)*(((d : ℝ)+1)*‖f‖)^2 := by
  classical
  apply exists_weakH2_of_gradient_test_bounds hS u (by positivity : 0 ≤ ((d : ℝ)+1)*‖f‖)
  intro i j φ
  have hc : ‖f‖*‖φ.toLp (volume.restrict S)‖ ≤
      (((d : ℝ)+1)*‖f‖)*‖φ.toLp (volume.restrict S)‖ := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d)
      (mul_nonneg (norm_nonneg f) (norm_nonneg (φ.toLp (volume.restrict S))))]
  by_cases hj : j=r
  · subst j
    by_cases hi : i=r
    · subst i
      let a (j : Fin d) := inner ℝ (derivativeComponent (Sym.cons j Sym.nil) (WeakSobolevJet.field 1 u))
        (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ j))
      have he := hf φ
      rw [weakGradientPairing_coordinates] at he
      simp only [φ.sobolevJet_derivative] at he
      change ∑ j, a j=inner ℝ f (φ.toLp (volume.restrict S)) at he
      have hab (j : Fin d) (hj : j ∈ Finset.univ.erase r) :
          |a j| ≤ ‖f‖*‖φ.toLp (volume.restrict S)‖ :=
        dirichlet_tangential_test_bound hS u hu f hf j (hSS j (Finset.mem_erase.mp hj).1) j φ
      have hs : |∑ j ∈ Finset.univ.erase r, a j| ≤ (d : ℝ)*(‖f‖*‖φ.toLp (volume.restrict S)‖) := by
        calc
          _ ≤ ∑ j ∈ Finset.univ.erase r, |a j| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j ∈ Finset.univ.erase r, ‖f‖*‖φ.toLp (volume.restrict S)‖ :=
            Finset.sum_le_sum hab
          _ ≤ ∑ _j : Fin d, ‖f‖*‖φ.toLp (volume.restrict S)‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => by positivity)
          _ = _ := by simp
      have har : a r=inner ℝ f (φ.toLp (volume.restrict S))-∑ j ∈ Finset.univ.erase r, a j := by
        have hh := Finset.sum_erase_add Finset.univ a (Finset.mem_univ r)
        linarith
      change |a r| ≤ _
      rw [har]
      calc
        _ ≤ |inner ℝ f (φ.toLp (volume.restrict S))|+|∑ j ∈ Finset.univ.erase r, a j| := abs_sub _ _
        _ ≤ ‖f‖*‖φ.toLp (volume.restrict S)‖+(d : ℝ)*(‖f‖*‖φ.toLp (volume.restrict S)‖) :=
          add_le_add (abs_real_inner_le_norm _ _) hs
        _ = _ := by ring
    · rw [weakGradient_test_mixed_commute u i r φ]
      exact (dirichlet_tangential_test_bound hS u hu f hf i (hSS i hi) r φ).trans hc
  · exact (dirichlet_tangential_test_bound hS u hu f hf j (hSS j hj) i φ).trans hc


theorem exists_halfspace_dirichlet_H2 (r : Fin d) (a : ℝ)
    (u : WeakSobolevJet d 1 (volume.restrict {x : SpatialCoordinates d | a < x r}) {x | a < x r})
    (hu : u ∈ dirichletJetSpace {x : SpatialCoordinates d | a < x r})
    (f : Lp ℝ 2 (volume.restrict {x : SpatialCoordinates d | a < x r}))
    (hf : IsWeakNegativeLaplacian u f) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict {x : SpatialCoordinates d | a < x r}) {x | a < x r},
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u ∧ negativeLaplacian U=f ∧
      ‖WeakSobolevJet.field 2 U‖^2 ≤
        (Fintype.card (Sym (Fin d) 2) : ℝ)*(((d : ℝ)+1)*‖f‖)^2 := by
  have hopen : IsOpen {x : SpatialCoordinates d | a < x r} :=
    isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r)
  have hSS : ∀ j : Fin d, j ≠ r → ∀ t : ℝ,
      (fun x => x+t • EuclideanSpace.basisFun (Fin d) ℝ j) ⁻¹' {x : SpatialCoordinates d | a < x r} ⊆
        {x | a < x r} := by
    intro j hj t x hx
    have hcoord : (x+t • EuclideanSpace.basisFun (Fin d) ℝ j) r=x r := by
      simp [EuclideanSpace.basisFun_apply,PiLp.add_apply,PiLp.smul_apply,Ne.symm hj]
    change a < (x+t • EuclideanSpace.basisFun (Fin d) ℝ j) r at hx
    change a < x r
    simpa only [hcoord] using hx
  obtain ⟨U,hU,hb⟩ := exists_dirichlet_H2_of_tangential_invariance hopen u hu f hf r hSS
  refine ⟨U,hU,?_,hb⟩
  have hw := negativeLaplacian_isWeak U
  rw [hU] at hw
  exact hw.unique_rhs hopen hf

end Carleman
