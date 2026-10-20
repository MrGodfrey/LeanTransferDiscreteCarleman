module
public import Carleman.Spatial.NonlinearGraphShear
/-! Actual weak Sobolev transport under the nonlinear graph shear.
All chain identities follow from the original distributional tests, the
actual inverse test pullback, and the true bounded slope multipliers.
The constructed full H¹ pullback is continuous, preserves H¹₀ through
its actual test closure, and has explicit value and gradient norm bounds. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {T : Set (SpatialCoordinates d)}

theorem IsWeakSpatialDerivative.graphShear_normal_pullback
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {u v : Lp ℝ 2 (volume.restrict T)}
    (hw : IsWeakSpatialDerivative (volume.restrict T) T (EuclideanSpace.basisFun (Fin d) ℝ r) u v) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    let hm := spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T
    IsWeakSpatialDerivative (volume.restrict (F ⁻¹' T)) (F ⁻¹' T)
      (EuclideanSpace.basisFun (Fin d) ℝ r) (homeomorphPullbackLp F hm u) (homeomorphPullbackLp F hm v) := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let hm := spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T
  have hST : F.symm ⁻¹' (F ⁻¹' T) ⊆ T := by
    intro x hx
    change F (F.symm x) ∈ T at hx
    simpa only [F.apply_symm_apply] using hx
  rw [IsWeakSpatialDerivative.iff_integral] at hw ⊢
  intro φ
  rw [integral_mul_homeomorphPullbackLp,integral_mul_homeomorphPullbackLp]
  let χ := φ.pullbackSmoothHomeomorph F.symm (spatialGraphShear_symm_contDiff r ψ hψ htrans) hST
  have hd (x) : fderiv ℝ χ.value x (EuclideanSpace.basisFun (Fin d) ℝ r)=
      fderiv ℝ φ.value (F.symm x) (EuclideanSpace.basisFun (Fin d) ℝ r) := by
    rw [SpatialTest.pullbackGraphShear_symm_derivative φ r ψ hψ htrans hST x (EuclideanSpace.basisFun (Fin d) ℝ r),spatialGraphShear_normal_derivative r ψ hψ htrans x]
    simp only [zero_mul,sub_zero]
    rfl
  have hh := hw χ
  simp_rw [hd] at hh
  exact hh

theorem IsWeakSpatialDerivative.mul_of_derivative_zero {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) {e : SpatialCoordinates d} {u v : Lp ℝ 2 (volume.restrict S)}
    (hu : IsWeakSpatialDerivative (volume.restrict S) S e u v)
    (w : BoundedMultiplier (volume.restrict S)) (hw : ContDiffOn ℝ ∞ w.value S)
    (hd : ∀ᵐ x ∂volume.restrict S, fderiv ℝ w.value x e=0) :
    IsWeakSpatialDerivative (volume.restrict S) S e (w.map u) (w.map v) := by
  let z : BoundedMultiplier (volume.restrict S) :=
    ⟨fun _ => 0,aestronglyMeasurable_const,0,le_rfl,Eventually.of_forall fun _ => by simp⟩
  have hz : z.map u=0 := by
    apply Lp.ext
    filter_upwards [z.map_ae u,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict S)] with x hx h0
    rw [hx,h0]
    simp only [z,zero_smul,Pi.zero_apply]
  have hdz : z.value =ᵐ[volume.restrict S] fun x => fderiv ℝ w.value x e := by
    filter_upwards [hd] with x hx
    exact hx.symm
  have hh := hu.mul hS (ae_restrict_mem hS.measurableSet) w z hw hdz
  simpa only [hz,add_zero] using hh

theorem IsWeakSpatialDerivative.graphShear_pullback (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    (i : Fin d) {u vi vr : Lp ℝ 2 (volume.restrict T)}
    (hi : IsWeakSpatialDerivative (volume.restrict T) T (EuclideanSpace.basisFun (Fin d) ℝ i) u vi)
    (hr : IsWeakSpatialDerivative (volume.restrict T) T (EuclideanSpace.basisFun (Fin d) ℝ r) u vr) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    let hm := spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T
    let w := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self
    IsWeakSpatialDerivative (volume.restrict (F ⁻¹' T)) (F ⁻¹' T)
      (EuclideanSpace.basisFun (Fin d) ℝ i) (homeomorphPullbackLp F hm u)
      (homeomorphPullbackLp F hm vi+w.map (homeomorphPullbackLp F hm vr)) := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let hm := spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T
  let P := homeomorphPullbackLp F hm
  let S := F ⁻¹' T
  let w := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure (ν := volume.restrict S) Measure.restrict_le_self
  have hS : IsOpen S := hT.preimage F.continuous
  have hST : F.symm ⁻¹' S ⊆ T := by
    intro x hx
    change F (F.symm x) ∈ T at hx
    simpa only [F.apply_symm_apply] using hx
  have hwr := hr.graphShear_normal_pullback r ψ hψ htrans
  have hp := hwr.mul_of_derivative_zero hS w (graphSlopeMultiplier_contDiff ψ hψ hC i).contDiffOn
    (Eventually.of_forall fun x => graphSlopeMultiplier_normal_derivative r ψ hψ hC htrans i x)
  change IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i) (P u) (P vi+w.map (P vr))
  intro φ
  let χ := φ.pullbackSmoothHomeomorph F.symm (spatialGraphShear_symm_contDiff r ψ hψ htrans) hST
  have hv : P (χ.toLp (volume.restrict T))=φ.toLp (volume.restrict S) := by
    apply Lp.ext
    filter_upwards [homeomorphPullbackLp_ae F hm (χ.toLp (volume.restrict T)),
      hm.quasiMeasurePreserving.ae (χ.toLp_ae (volume.restrict T)),φ.toLp_ae (volume.restrict S)] with x hx hy hz
    rw [hx]
    change χ.toLp (volume.restrict T) (F x)=_
    rw [hy,hz]
    exact congrArg φ.value (F.symm_apply_apply x)
  have hd : P (χ.derivativeLp (volume.restrict T) (EuclideanSpace.basisFun (Fin d) ℝ i))=
      φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)-
        w.map (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ r)) := by
    apply Lp.ext
    filter_upwards [homeomorphPullbackLp_ae F hm (χ.derivativeLp (volume.restrict T) (EuclideanSpace.basisFun (Fin d) ℝ i)),
      hm.quasiMeasurePreserving.ae (χ.derivativeLp_ae (volume.restrict T) (EuclideanSpace.basisFun (Fin d) ℝ i)),
      φ.derivativeLp_ae (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i),
      φ.derivativeLp_ae (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ r),
      w.map_ae (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ r)),
      Lp.coeFn_sub (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i))
        (w.map (φ.derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ r)))] with x hx hy hdi hdr hw hs
    rw [hx]
    change χ.derivativeLp (volume.restrict T) (EuclideanSpace.basisFun (Fin d) ℝ i) (F x)=_
    rw [hy,hs]
    simp only [Pi.sub_apply,hw,hdi,hdr,smul_eq_mul]
    rw [SpatialTest.pullbackGraphShear_symm_derivative φ r ψ hψ htrans hST (F x) (EuclideanSpace.basisFun (Fin d) ℝ i)]
    change fderiv ℝ φ.value (F.symm (F x)) _ - fderiv ℝ ψ (F x) _ * fderiv ℝ φ.value (F.symm (F x)) _ = _
    rw [F.symm_apply_apply]
    have hi' := spatialGraphShear_fderiv_invariant r ψ hψ htrans x (ψ x)
    change fderiv ℝ ψ (F x)=fderiv ℝ ψ x at hi'
    rw [hi']
    rfl
  have he := hi χ
  rw [← P.inner_map_map u _,← P.inner_map_map vi _,hd,hv,inner_sub_right] at he
  have hpφ := hp φ
  rw [w.inner_map_left] at hpφ
  change inner ℝ (P u) _ = -inner ℝ (P vi+w.map (P vr)) _
  rw [inner_add_left]
  linarith

namespace WeakSobolevJet
variable (hT : IsOpen T) (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
  {C : NNReal} (hC : LipschitzWith C ψ)
  (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)

def graphShearPullback (u : WeakSobolevJet d 1 (volume.restrict T) T) :
    WeakSobolevJet d 1 (volume.restrict (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T))
      (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T) :=
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let hm := spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T
  let P := homeomorphPullbackLp F hm
  let w i := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure
    (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self
  firstComponentJet (P (value u)) (fun i => P (derivativeComponent (Sym.cons i Sym.nil) (field 1 u))+
    (w i).map (P (derivativeComponent (Sym.cons r Sym.nil) (field 1 u))))
    (fun i => (u.property 0 Sym.nil i).graphShear_pullback hT r ψ hψ hC htrans i (u.property 0 Sym.nil r))

theorem graphShearPullback_value (u : WeakSobolevJet d 1 (volume.restrict T) T) :
    value (graphShearPullback hT r ψ hψ hC htrans u)=
      homeomorphPullbackLp (spatialGraphShear r ψ hψ.continuous htrans)
        (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T) (value u) :=
  by
    unfold graphShearPullback
    exact firstComponentJet_value _ _ _

theorem graphShearPullback_gradient (u : WeakSobolevJet d 1 (volume.restrict T) T) (i : Fin d) :
    let F := spatialGraphShear r ψ hψ.continuous htrans
    let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
    let w := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self
    derivativeComponent (Sym.cons i Sym.nil) (field 1 (graphShearPullback hT r ψ hψ hC htrans u))=
      P (derivativeComponent (Sym.cons i Sym.nil) (field 1 u))+
        w.map (P (derivativeComponent (Sym.cons r Sym.nil) (field 1 u))) :=
  by
    unfold graphShearPullback
    exact firstComponentJet_gradient _ _ _ i

theorem graphShearPullback_tendsto {U : ℕ → WeakSobolevJet d 1 (volume.restrict T) T}
    {u : WeakSobolevJet d 1 (volume.restrict T) T} (ht : Tendsto U atTop (𝓝 u)) :
    Tendsto (fun n => graphShearPullback hT r ψ hψ hC htrans (U n)) atTop
      (𝓝 (graphShearPullback hT r ψ hψ hC htrans u)) := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
  let w i := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self
  have hg (i : Fin d) : Tendsto (fun n => P (derivativeComponent (Sym.cons i Sym.nil) (field 1 (U n)))) atTop
      (𝓝 (P (derivativeComponent (Sym.cons i Sym.nil) (field 1 u)))) :=
    (P.continuous.tendsto _).comp (((derivativeComponentCLM (Sym.cons i Sym.nil)).continuous.tendsto _).comp
      ((fieldCLM 1).continuous.tendsto u |>.comp ht))
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro k
  fin_cases k
  · change Tendsto (fun n => (OperatorMultiplier.const scalarZeroFiber).continuousLinearMap (P (value (U n)))) atTop
      (𝓝 ((OperatorMultiplier.const scalarZeroFiber).continuousLinearMap (P (value u))))
    exact ((OperatorMultiplier.const scalarZeroFiber).continuousLinearMap.continuous.tendsto _).comp
      ((P.continuous.tendsto _).comp (valueCLM.continuous.tendsto u |>.comp ht))
  · change Tendsto (fun n => firstGradientAssembly (fun i => P (derivativeComponent (Sym.cons i Sym.nil) (field 1 (U n)))+
        (w i).map (P (derivativeComponent (Sym.cons r Sym.nil) (field 1 (U n)))))) atTop
      (𝓝 (firstGradientAssembly (fun i => P (derivativeComponent (Sym.cons i Sym.nil) (field 1 u))+
        (w i).map (P (derivativeComponent (Sym.cons r Sym.nil) (field 1 u))))))
    apply (firstGradientAssembly.continuous.tendsto _).comp
    apply tendsto_pi_nhds.mpr
    intro i
    exact (hg i).add (((w i).continuousLinearMap.continuous.tendsto _).comp (hg r))

theorem graphShearPullback_test (φ : SpatialTest T) :
    graphShearPullback hT r ψ hψ hC htrans φ.sobolevJet =
      (φ.pullbackSmoothHomeomorph (spatialGraphShear r ψ hψ.continuous htrans)
        (spatialGraphShear_contDiff r ψ hψ htrans) Subset.rfl).sobolevJet := by
  have hopen := hT.preimage (spatialGraphShear r ψ hψ.continuous htrans).continuous
  apply value_injective hopen (ae_restrict_mem hopen.measurableSet)
  rw [graphShearPullback_value,φ.sobolevJet_value,SpatialTest.sobolevJet_value,
    SpatialTest.pullbackSmoothHomeomorph_toLp _ _ _ _ (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)]

theorem graphShearPullback_dirichlet (u : WeakSobolevJet d 1 (volume.restrict T) T)
    (hu : u ∈ dirichletJetSpace T) :
    graphShearPullback hT r ψ hψ hC htrans u ∈
      dirichletJetSpace (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T) := by
  obtain ⟨U,hU,ht⟩ := (mem_closure_iff_seq_limit).mp hu
  choose φ hφ using fun n => exists_test_of_mem_test_span hT (hU n)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (graphShearPullback_tendsto hT r ψ hψ hC htrans ht)
  apply Eventually.of_forall
  intro n
  rw [← hφ n,graphShearPullback_test]
  exact test_mem_dirichletJetSpace _ _

theorem graphShearPullback_value_norm (u : WeakSobolevJet d 1 (volume.restrict T) T) :
    ‖value (graphShearPullback hT r ψ hψ hC htrans u)‖=‖value u‖ := by
  rw [graphShearPullback_value]
  exact (homeomorphPullbackLp _ _).norm_map _

theorem graphShearPullback_gradient_bound (u : WeakSobolevJet d 1 (volume.restrict T) T) :
    ‖field 1 (graphShearPullback hT r ψ hψ hC htrans u)‖^2 ≤
      (d : ℝ)*((1+(C : ℝ))*‖field 1 u‖)^2 := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
  let w i := (graphSlopeMultiplier ψ hψ hC i).restrictMeasure (ν := volume.restrict (F ⁻¹' T)) Measure.restrict_le_self
  let G i := derivativeComponent (Sym.cons i Sym.nil) (field 1 u)
  change ‖firstGradientAssembly (fun i => P (G i)+(w i).map (P (G r)))‖^2 ≤ _
  rw [firstGradientAssembly_norm_sq]
  have hn (i : Fin d) : ‖P (G i)+(w i).map (P (G r))‖ ≤ (1+(C : ℝ))*‖field 1 u‖ := by
    apply (norm_add_le _ _).trans
    have hw := (w i).seminorm_le (P (G r))
    change ‖(w i).map (P (G r))‖ ≤ (C : ℝ)*‖P (G r)‖ at hw
    rw [P.norm_map] at hw ⊢
    calc
      _ ≤ ‖G i‖+(C : ℝ)*‖G r‖ := add_le_add le_rfl hw
      _ ≤ ‖field 1 u‖+(C : ℝ)*‖field 1 u‖ := add_le_add (derivativeComponent_norm_le _ _)
        (mul_le_mul_of_nonneg_left (derivativeComponent_norm_le _ _) C.coe_nonneg)
      _ = _ := by ring
  calc
    _ ≤ ∑ _i : Fin d, ((1+(C : ℝ))*‖field 1 u‖)^2 := Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hn i) 2
    _ = _ := by simp

end WeakSobolevJet
end Carleman
