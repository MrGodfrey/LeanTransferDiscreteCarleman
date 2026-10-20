module
public import Carleman.Spatial.WeakConvexHessian
public import Carleman.Spatial.ClassicalHarmonicTimeCore
public import Carleman.Continuous.RegularTimeCore
/-! The actual smooth inner-domain Dirichlet operator and periodic graph density. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem exists_smooth_operator_graph_approximation_of_H2 (hS : IsOpen S) (hd : 0<d)
    (hb : Bornology.IsBounded S)
    (z : (boundedDirichletOriginalForm hS hd hb).model.operatorGraph)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hv : WeakSobolevJet.value u=(boundedDirichletOriginalForm hS hd hb).model.graphH z)
    (hA : negativeLaplacian u=(boundedDirichletOriginalForm hS hd hb).model.graphA z)
    (hu : HasSmoothDirichletH2Approximation u) :
    let B := (boundedDirichletOriginalForm hS hd hb).model
    ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)), ∃ Z : ℕ → B.operatorGraph,
      (∀ n, ∀ x ∈ frontier S, (U n).value x=0) ∧
      (∀ n, B.graphH (Z n)=(U n).toLp (volume.restrict S)) ∧
      (∀ n, B.graphA (Z n)= -(U n).laplacianOnLp S) ∧ Tendsto Z atTop (𝓝 z) := by
  let B := (boundedDirichletOriginalForm hS hd hb).model
  obtain ⟨U,hUb,hUD,ht⟩ := hu
  have hmem (n : ℕ) : WeakSobolevJet.value ((U n).allOrderJetOn S 2)∈dirichletSubspace S :=
    (mem_dirichletJetSpace_iff S hS _).mp (hUD n)
  let zn (n : ℕ) := dirichletH2DomainElement hS hd hb ((U n).allOrderJetOn S 2) (hmem n)
  let Z (n : ℕ) := B.graphOfDomain (zn n)
  have hzn (n : ℕ) : (zn n : Lp ℝ 2 (volume.restrict S))=(U n).toLp (volume.restrict S) :=
    (U n).allOrderJetOn_value S 2
  have hAn (n : ℕ) : B.operator (zn n)= -(U n).laplacianOnLp S :=
    (dirichletH2DomainElement_operator hS hd hb _ _).trans ((U n).allOrderJetOn_negativeLaplacian S)
  refine ⟨U,Z,hUb,hzn,hAn,?_⟩
  have ht0 : Tendsto (fun n => (U n).toLp (volume.restrict S)) atTop (𝓝 (B.graphH z)) := by
    have hh := (WeakSobolevJet.valueCLM.continuous.tendsto u).comp ht
    simpa only [Function.comp_def,WeakSobolevJet.valueCLM_apply,SpatialTest.allOrderJetOn_value,hv] using hh
  have htA : Tendsto (fun n => -(U n).laplacianOnLp S) atTop (𝓝 (B.graphA z)) := by
    have hh := ((negativeLaplacian (d := d) (S := S)).continuous.tendsto u).comp ht
    simpa only [Function.comp_def,SpatialTest.allOrderJetOn_negativeLaplacian,hA] using hh
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => ((zn n : Lp ℝ 2 (volume.restrict S)), B.operator (zn n))) atTop (𝓝 z.val)
  have heA : (fun n => B.operator (zn n))=(fun n => -(U n).laplacianOnLp S) := funext hAn
  change Tendsto (fun n => ((zn n : Lp ℝ 2 (volume.restrict S)), (fun n => B.operator (zn n)) n)) atTop (𝓝 z.val)
  rw [heA]
  simp only [hzn]
  exact ht0.prodMk_nhds htA

theorem exists_halfspaceSmoothInner_operator_graph_approximation {ι : Type*} [Fintype ι]
    (hd : 0<d) (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {c : SpatialCoordinates d} (hc : c∈halfspaceSmoothInner ℓ b n) :
    let S := halfspaceSmoothInner ℓ b n
    let hS := halfspaceSmoothInner_open ℓ b n
    let hb := (halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure
    let B := (boundedDirichletOriginalForm hS hd hb).model
    ∀ z : B.operatorGraph,
      ∃ U : ℕ → SpatialTest (univ : Set (SpatialCoordinates d)), ∃ Z : ℕ → B.operatorGraph,
        (∀ k, ∀ x ∈ frontier S, (U k).value x=0) ∧
        (∀ k, B.graphH (Z k)=(U k).toLp (volume.restrict S)) ∧
        (∀ k, B.graphA (Z k)= -(U k).laplacianOnLp S) ∧ Tendsto Z atTop (𝓝 z) := by
  intro S hS hb B z
  obtain ⟨u,huz,hu,huf⟩ := (dirichlet_operator_graph_iff hS hd hb (B.graphH z) (B.graphA z)).mp
    ⟨B.graphDomain z,rfl,B.graphDomain_operator z⟩
  obtain ⟨v,hv,hvf⟩ := halfspaceSmoothInner_dirichlet_H2 ℓ b n hbounded hc u hu (B.graphA z) huf
  have hvD : WeakSobolevJet.truncate (by decide : 1≤2) v∈dirichletJetSpace S := by rwa [hv]
  apply exists_smooth_operator_graph_approximation_of_H2 hS hd hb z v
    ((congrArg WeakSobolevJet.value hv).trans huz) hvf
  exact halfspaceSmoothInner_strong_h2_approximation hd ℓ b n hbounded hc ⟨v,hvD⟩

theorem halfspaceSmoothInner_classicalTimeCore_dense {ι : Type*} [Fintype ι]
    (hd : 0<d) (ℓ : ι → SpatialCoordinates d →L[ℝ] ℝ) (b : ι → ℝ) (n : ℕ)
    (hbounded : Bornology.IsBounded {x | ∀ i, b i<ℓ i x})
    {c : SpatialCoordinates d} (hc : c∈halfspaceSmoothInner ℓ b n) (g : TimeGrid) :
    let hS := halfspaceSmoothInner_open ℓ b n
    let hb := (halfspaceSmoothInner_compact ℓ b hbounded n).isBounded.subset subset_closure
    Dense (classicalDirichletTimeCore hS hd hb g : Set
      ((boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g)) := by
  intro hS hb
  let B := (boundedDirichletOriginalForm hS hd hb).model
  let K := classicalDirichletTimeCore hS hd hb g
  apply B.dense_of_harmonic_approximation g K
  intro j x y
  obtain ⟨U,X,hUb,hUX,hUA,hX⟩ := exists_halfspaceSmoothInner_operator_graph_approximation hd ℓ b n hbounded hc x
  obtain ⟨V,Y,hVb,hVY,hVA,hY⟩ := exists_halfspaceSmoothInner_operator_graph_approximation hd ℓ b n hbounded hc y
  refine ⟨X,Y,hX,hY,?_⟩
  intro k
  exact harmonicGraph_mem_classicalDirichletTimeCore hS hd hb g j (X k) (Y k) (U k) (V k)
    (hUX k) (hVY k) (hUA k) (hVA k) (hUb k) (hVb k)

end Carleman
