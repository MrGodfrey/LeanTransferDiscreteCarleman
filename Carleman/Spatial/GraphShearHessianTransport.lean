module
public import Carleman.Spatial.GraphShearWeakTransport
/-! Full H² transport through the actual nonlinear graph shear.
The second weak chain rule is obtained from the first weak transport and
actual bounded coefficient derivatives. The inverse shear supplies the
converse for precisely the same original H¹ state, with explicit bounds. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {T : Set (SpatialCoordinates d)}

theorem exists_graphShearPullback_H2 (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (U : WeakSobolevJet d 2 (volume.restrict T) T) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    let u := WeakSobolevJet.truncate (by omega : 1 ≤ 2) U
    let L := (1+(C : ℝ))^2*‖WeakSobolevJet.field 2 U‖+(∑ i, (B i : ℝ))*‖WeakSobolevJet.field 1 U‖
    ∃ V : WeakSobolevJet d 2 (volume.restrict (F ⁻¹' T)) (F ⁻¹' T),
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) V=WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u ∧
      ‖WeakSobolevJet.field 2 V‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*L^2 := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let S := F ⁻¹' T
  let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
  let u := WeakSobolevJet.truncate (by omega : 1 ≤ 2) U
  let v := WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u
  let G i := derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 U)
  let H i j := derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 U)
  let w i := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure (ν := volume.restrict S) Measure.restrict_le_self
  have hS : IsOpen S := hT.preimage F.continuous
  let dw i j := (graphSlopeMultiplier ψ hψ hC i).spatialDerivativeOn hS
    (graphSlopeMultiplier_contDiff ψ hψ hC i).contDiffOn (hB i) j
  let Q i j := P (H i j)+(w j).map (P (H i r))
  have hQ (i j : Fin d) : IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ j) (P (G i)) (Q i j) :=
    (U.property 1 (Sym.cons i Sym.nil) j).graphShear_pullback hT r ψ hψ hC htrans j
      (U.property 1 (Sym.cons i Sym.nil) r)
  have hgrad (i : Fin d) : derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 v)=
      P (G i)+(w i).map (P (G r)) :=
    WeakSobolevJet.graphShearPullback_gradient hT r ψ hψ hC htrans u i
  have hD (i j : Fin d) : IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ j)
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 v))
      (Q i j+((w i).map (Q r j)+(dw i j).map (P (G r)))) := by
    rw [hgrad]
    exact (hQ i j).add ((hQ r j).mul hS (ae_restrict_mem hS.measurableSet) (w i) (dw i j)
      (graphSlopeMultiplier_contDiff ψ hψ hC i).contDiffOn (Eventually.of_forall fun _ => rfl))
  have hH (i j : Fin d) : ‖P (H i j)‖ ≤ ‖WeakSobolevJet.field 2 U‖ := by
    rw [P.norm_map]
    exact derivativeComponent_norm_le _ _
  have hG (i : Fin d) : ‖P (G i)‖ ≤ ‖WeakSobolevJet.field 1 U‖ := by
    rw [P.norm_map]
    exact derivativeComponent_norm_le _ _
  have hQn (i j : Fin d) : ‖Q i j‖ ≤ (1+(C : ℝ))*‖WeakSobolevJet.field 2 U‖ := by
    apply (norm_add_le _ _).trans
    have hw := (w j).seminorm_le (P (H i r))
    change ‖(w j).map (P (H i r))‖ ≤ (C : ℝ)*‖P (H i r)‖ at hw
    calc
      _ ≤ ‖WeakSobolevJet.field 2 U‖+(C : ℝ)*‖WeakSobolevJet.field 2 U‖ :=
        add_le_add (hH i j) (hw.trans (mul_le_mul_of_nonneg_left (hH i r) C.coe_nonneg))
      _ = _ := by ring
  have hN (i j : Fin d) : ‖Q i j+((w i).map (Q r j)+(dw i j).map (P (G r)))‖ ≤
      (1+(C : ℝ))^2*‖WeakSobolevJet.field 2 U‖+(∑ i, (B i : ℝ))*‖WeakSobolevJet.field 1 U‖ := by
    have hw := (w i).seminorm_le (Q r j)
    have hd := (dw i j).seminorm_le (P (G r))
    change ‖(w i).map (Q r j)‖ ≤ (C : ℝ)*‖Q r j‖ at hw
    change ‖(dw i j).map (P (G r))‖ ≤ (B i : ℝ)*‖P (G r)‖ at hd
    have hBi : (B i : ℝ) ≤ ∑ k, (B k : ℝ) :=
      Finset.single_le_sum (fun k _ => (B k).coe_nonneg) (Finset.mem_univ i)
    calc
      _ ≤ ‖Q i j‖+(‖(w i).map (Q r j)‖+‖(dw i j).map (P (G r))‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ (1+(C : ℝ))*‖WeakSobolevJet.field 2 U‖+
          ((C : ℝ)*((1+(C : ℝ))*‖WeakSobolevJet.field 2 U‖)+(∑ k, (B k : ℝ))*‖WeakSobolevJet.field 1 U‖) :=
        add_le_add (hQn i j) (add_le_add (hw.trans (mul_le_mul_of_nonneg_left (hQn r j) C.coe_nonneg))
          (hd.trans ((mul_le_mul_of_nonneg_left (hG r) (B i).coe_nonneg).trans
            (mul_le_mul_of_nonneg_right hBi (norm_nonneg _)))))
      _ = _ := by ring
  apply exists_weakH2_of_gradient_test_bounds hS v (by positivity)
  intro i j φ
  rw [hD i j φ,abs_neg]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hN i j) (norm_nonneg _))

theorem exists_graphShearPullback_H2_ae (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (U : WeakSobolevJet d 2 (volume.restrict T) T) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    let L := (1+(C : ℝ))^2*‖WeakSobolevJet.field 2 U‖+(∑ i, (B i : ℝ))*‖WeakSobolevJet.field 1 U‖
    ∃ V : WeakSobolevJet d 2 (volume.restrict (F ⁻¹' T)) (F ⁻¹' T),
      WeakSobolevJet.value V =ᵐ[volume.restrict (F ⁻¹' T)] WeakSobolevJet.value U ∘ F ∧
      ‖WeakSobolevJet.field 2 V‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*L^2 := by
  obtain ⟨V,hV,hn⟩ := exists_graphShearPullback_H2 hT r ψ hψ hC htrans hB U
  refine ⟨V,?_,hn⟩
  have he := congrArg WeakSobolevJet.value hV
  rw [WeakSobolevJet.graphShearPullback_value] at he
  change WeakSobolevJet.value V=_ at he
  rw [he]
  exact homeomorphPullbackLp_ae _ _ _

theorem spatialGraphShear_neg_eq_symm (r : Fin d) (ψ : SpatialCoordinates d → ℝ)
    (hψ : Continuous ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    spatialGraphShear r (fun x => -ψ x) hψ.neg (fun x t => congrArg Neg.neg (htrans x t))=
      (spatialGraphShear r ψ hψ htrans).symm := by
  apply Homeomorph.ext
  intro x
  change x+(-ψ x) • EuclideanSpace.basisFun (Fin d) ℝ r=x-ψ x • EuclideanSpace.basisFun (Fin d) ℝ r
  rw [neg_smul,sub_eq_add_neg]

theorem graphSlopeMultiplier_neg (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ) (i : Fin d) :
    (graphSlopeMultiplier (fun x => -ψ x) hψ.neg hC.neg i).value =
      fun x => -(graphSlopeMultiplier ψ hψ hC i).value x := by
  funext x
  change fderiv ℝ (fun y => -ψ y) x (EuclideanSpace.basisFun (Fin d) ℝ i) = _
  rw [fderiv_fun_neg]
  rfl

theorem exists_H2_of_graphShearPullback_H2 (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (u : WeakSobolevJet d 1 (volume.restrict T) T)
    (V : WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
    (hV : WeakSobolevJet.truncate (by omega : 1 ≤ 2) V=WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u) :
    let L := (1+(C : ℝ))^2*‖WeakSobolevJet.field 2 V‖+(∑ i, (B i : ℝ))*‖WeakSobolevJet.field 1 V‖
    ∃ U : WeakSobolevJet d 2 (volume.restrict T) T,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u ∧
      ‖WeakSobolevJet.field 2 U‖^2 ≤ (Fintype.card (Sym (Fin d) 2) : ℝ)*L^2 := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let S := F ⁻¹' T
  have hS : IsOpen S := hT.preimage F.continuous
  have hntrans (x : SpatialCoordinates d) (t : ℝ) : -(ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r))= -ψ x :=
    congrArg Neg.neg (htrans x t)
  have hBn (i : Fin d) : LipschitzWith (B i) (graphSlopeMultiplier (fun x => -ψ x) hψ.neg hC.neg i).value := by
    rw [graphSlopeMultiplier_neg]
    exact (hB i).neg
  have hh := exists_graphShearPullback_H2_ae hS r (fun x => -ψ x) hψ.neg hC.neg hntrans hBn V
  dsimp only at hh
  rw [spatialGraphShear_neg_eq_symm] at hh
  have hdom : F.symm ⁻¹' S=T := by
    ext x
    change F (F.symm x) ∈ T ↔ x ∈ T
    rw [F.apply_symm_apply]
  change ∃ U : WeakSobolevJet d 2 (volume.restrict (F.symm ⁻¹' S)) (F.symm ⁻¹' S),
    WeakSobolevJet.value U =ᵐ[volume.restrict (F.symm ⁻¹' S)] WeakSobolevJet.value V ∘ F.symm ∧ _ at hh
  rw [hdom] at hh
  obtain ⟨U,hU,hn⟩ := hh
  refine ⟨U,?_,hn⟩
  apply WeakSobolevJet.value_injective hT (ae_restrict_mem hT.measurableSet)
  change WeakSobolevJet.value U=WeakSobolevJet.value u
  have hv := congrArg WeakSobolevJet.value hV
  rw [WeakSobolevJet.graphShearPullback_value] at hv
  change WeakSobolevJet.value V=homeomorphPullbackLp F
    (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T) (WeakSobolevJet.value u) at hv
  have hm := spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T
  have hae := (hm.symm F.toMeasurableEquiv).quasiMeasurePreserving.ae
    (homeomorphPullbackLp_ae F hm (WeakSobolevJet.value u))
  apply Lp.ext
  filter_upwards [hU,hae] with x hx hy
  rw [hv] at hx
  have hy' : homeomorphPullbackLp F hm (WeakSobolevJet.value u) (F.symm x)=
      WeakSobolevJet.value u (F (F.symm x)) := hy
  simpa only [Function.comp_apply,F.apply_symm_apply] using hx.trans hy'

theorem graphShearPullback_H2_iff (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) :
    (∃ U : WeakSobolevJet d 2 (volume.restrict T) T, WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u) ↔
    ∃ V : WeakSobolevJet d 2 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
        (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T),
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) V=WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u := by
  constructor
  · rintro ⟨U,hU⟩
    obtain ⟨V,hV,_⟩ := exists_graphShearPullback_H2 hT r ψ hψ hC htrans hB U
    exact ⟨V,by simpa only [hU] using hV⟩
  · rintro ⟨V,hV⟩
    obtain ⟨U,hU,_⟩ := exists_H2_of_graphShearPullback_H2 hT r ψ hψ hC htrans hB u V hV
    exact ⟨U,hU⟩

end Carleman
