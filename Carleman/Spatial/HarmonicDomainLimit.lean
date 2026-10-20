module
public import Carleman.Spatial.InnerGraphLimit
public import Carleman.Spatial.DirichletHarmonicFields
public import Carleman.Spatial.DirichletHeatFields
public import Carleman.Continuous.HarmonicLpMap
/-! Genuine periodic inner states converge in all four original ambient heat fields. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_dirichlet_exhaustion_harmonic_field_approximation (hS : IsOpen S) (hd : 0<d)
    (hb : Bornology.IsBounded S)
    (T : ℕ → Set (SpatialCoordinates d)) (hT : ∀ n, IsOpen (T n)) (hTS : ∀ n, T n⊆S)
    (hm : Monotone T) (hcover : S⊆⋃ n, T n) (g : TimeGrid) (j : ℤ) :
    let B := (boundedDirichletOriginalForm hS hd hb).model
    let Bn := fun n => (boundedDirichletOriginalForm (hT n) hd (hb.subset (hTS n))).model
    ∀ x y : B.operatorGraph, ∃ P : ∀ n, (Bn n).PeriodicGraph g,
      Tendsto (fun n => subdomainHeatFields S (T n) g
        (dirichletHeatFields (hT n) hd (hb.subset (hTS n)) g (P n))) atTop
        (𝓝 (dirichletHeatFields hS hd hb g (B.harmonicGraph g j x y))) := by
  intro B Bn x y
  have happrox := exists_dirichlet_exhaustion_graph_approximation (d := d) (S := S) hS hd hb T hT hTS hm hcover
  have hx := happrox x
  obtain ⟨X,_hXA,hX0,hXG,hXA⟩ := hx
  have hy := happrox y
  obtain ⟨Y,_hYA,hY0,hYG,hYA⟩ := hy
  have hE (n : ℕ) (v : Lp ℝ 2 (volume.restrict (T n))) :
      subdomainZeroExtendCLM S (T n) v=subdomainZeroExtend S (hT n).measurableSet v :=
    subdomainZeroExtendCLM_apply (hT n).measurableSet v
  let P (n : ℕ) := (Bn n).harmonicGraph g j (X n) (Y n)
  refine ⟨P,?_⟩
  have hX0' : Tendsto (fun n => subdomainZeroExtendCLM S (T n) ((Bn n).graphH (X n))) atTop (𝓝 (B.graphH x)) := by
    simpa only [hE] using hX0
  have hY0' : Tendsto (fun n => subdomainZeroExtendCLM S (T n) ((Bn n).graphH (Y n))) atTop (𝓝 (B.graphH y)) := by
    simpa only [hE] using hY0
  have hXA' : Tendsto (fun n => subdomainZeroExtendCLM S (T n) ((Bn n).graphA (X n))) atTop (𝓝 (B.graphA x)) := by
    simpa only [hE] using hXA
  have hYA' : Tendsto (fun n => subdomainZeroExtendCLM S (T n) ((Bn n).graphA (Y n))) atTop (𝓝 (B.graphA y)) := by
    simpa only [hE] using hYA
  have hXG' : Tendsto (fun n => subdomainZeroExtendCLM S (T n)
      (WeakSobolevJet.field 1 (dirichletDomainJet (hT n) hd (hb.subset (hTS n)) ((Bn n).graphDomain (X n)))))
      atTop (𝓝 (WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (B.graphDomain x)))) := by
    exact hXG.congr' (Filter.Eventually.of_forall (fun n =>
      (subdomainZeroExtendCLM_apply (hT n).measurableSet _).symm))
  have hYG' : Tendsto (fun n => subdomainZeroExtendCLM S (T n)
      (WeakSobolevJet.field 1 (dirichletDomainJet (hT n) hd (hb.subset (hTS n)) ((Bn n).graphDomain (Y n)))))
      atTop (𝓝 (WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (B.graphDomain y)))) := by
    exact hYG.congr' (Filter.Eventually.of_forall (fun n =>
      (subdomainZeroExtendCLM_apply (hT n).measurableSet _).symm))
  have h0 := g.harmonicLp_tendsto j hX0' hY0'
  have hD := g.harmonicLp_tendsto j (hY0'.const_smul (g.angularFrequency j)) (hX0'.const_smul (-g.angularFrequency j))
  have hA := g.harmonicLp_tendsto j hXA' hYA'
  have hG := g.harmonicLp_tendsto j hXG' hYG'
  simp only [subdomainHeatFields_apply,dirichletHeatFields_apply,P,B,Bn,
    dirichlet_harmonic_value_Lp,dirichlet_harmonic_derivative_Lp,dirichlet_harmonic_operator_Lp,
    dirichlet_harmonic_gradient_Lp,TimeGrid.compLp_harmonic,map_smul]
  exact h0.prodMk_nhds (hD.prodMk_nhds (hA.prodMk_nhds hG))

end Carleman
