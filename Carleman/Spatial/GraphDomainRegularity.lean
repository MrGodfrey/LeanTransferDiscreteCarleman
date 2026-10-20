module
public import Carleman.Spatial.GraphEllipticForm
/-! The original weak Dirichlet Poisson state is H² on actual smooth graph
epigraphs and hypographs. Coefficients and all transformed equation inputs
are supplied internally, and inverse transport preserves the same state. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

theorem exists_dirichlet_H2_of_graph_tangential_invariance
    {T : Set (SpatialCoordinates d)} (hT : IsOpen T)
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (u : WeakSobolevJet d 1 (volume.restrict T) T)
    (hu : u ∈ dirichletJetSpace T)
    (f : Lp ℝ 2 (volume.restrict T))
    (hf : IsWeakNegativeLaplacian u f)
    (hSS : ∀ j : Fin d, j ≠ r → ∀ t : ℝ,
      (fun x => x+t • EuclideanSpace.basisFun (Fin d) ℝ j) ⁻¹' (spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T) ⊆
        spatialGraphShear r ψ hψ.continuous htrans ⁻¹' T) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict T) T,
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u := by
  let F := spatialGraphShear r ψ hψ.continuous htrans
  let S := F ⁻¹' T
  have hS : IsOpen S := hT.preimage F.continuous
  let v := WeakSobolevJet.graphShearPullback hT r ψ hψ hC htrans u
  have hv : v ∈ dirichletJetSpace S := WeakSobolevJet.graphShearPullback_dirichlet hT r ψ hψ hC htrans u hu
  let a := graphEllipticCoefficient r ψ hψ hC
  let L : Fin d → Fin d → NNReal := fun _ _ => 2*(1+(d : NNReal)*C)*(∑ i, B i)
  let κ : ℝ := ((1+(d : ℝ)*C)^2)⁻¹
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have ha (i j) : ContDiffOn ℝ ∞ (a i j).value S := (graphEllipticCoefficient_contDiff r ψ hψ hC i j).contDiffOn
  have hL (i j) : LipschitzWith (L i j) (a i j).value := graphEllipticCoefficient_lipschitz r ψ hψ hC B hB i j
  have hA : ∀ᵐ x ∂volume, ∀ ξ : Fin d → ℝ, κ*(∑ i, (ξ i)^2) ≤ ∑ i, ∑ j, (a i j).value x*(ξ i)*(ξ j) :=
    Eventually.of_forall (graphEllipticCoefficient_elliptic r ψ hψ hC htrans)
  let P := homeomorphPullbackLp F (spatialGraphShear_measurePreserving_restrict r ψ hψ htrans T)
  have heq (φ : SpatialTest S) : matrixGradientPairing a (WeakSobolevJet.zeroExtendDirichlet hS v hv) φ.fullJet=
      inner ℝ (P f) (φ.toLp (volume.restrict S)) := by
    rw [matrixGradientPairing_test_integral]
    exact graphShearPullback_equation_integral hT r ψ hψ hC htrans u f hf φ
  obtain ⟨V,hV,_hbound⟩ := exists_variable_dirichlet_H2_of_tangential_invariance hS v hv a ha hL hκ hA (P f) heq r hSS
  obtain ⟨U,hU,_hbound⟩ := exists_H2_of_graphShearPullback_H2 hT r ψ hψ hC htrans hB u V hV
  exact ⟨U,hU⟩

theorem exists_graphEpigraph_dirichlet_H2
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (u : WeakSobolevJet d 1 (volume.restrict {x : SpatialCoordinates d | ψ x < x r}) {x | ψ x < x r})
    (hu : u ∈ dirichletJetSpace {x : SpatialCoordinates d | ψ x < x r})
    (f : Lp ℝ 2 (volume.restrict {x : SpatialCoordinates d | ψ x < x r}))
    (hf : IsWeakNegativeLaplacian u f) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict {x : SpatialCoordinates d | ψ x < x r}) {x | ψ x < x r},
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u := by
  have hT : IsOpen {x : SpatialCoordinates d | ψ x < x r} := isOpen_lt hψ.continuous (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r)
  apply exists_dirichlet_H2_of_graph_tangential_invariance hT r ψ hψ hC htrans hB u hu f hf
  rw [spatialGraphShear_halfspace]
  intro j hj t x hx
  have hc : (x+t • EuclideanSpace.basisFun (Fin d) ℝ j) r=x r := by
    simp [EuclideanSpace.basisFun_apply,PiLp.add_apply,PiLp.smul_apply,Ne.symm hj]
  change 0 < (x+t • EuclideanSpace.basisFun (Fin d) ℝ j) r at hx
  change 0 < x r
  rwa [hc] at hx

theorem spatialGraphShear_hypograph (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : Continuous ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x) :
    spatialGraphShear r ψ hψ htrans ⁻¹' {x | x r < ψ x} = {x | x r < 0} := by
  ext x
  change (x+ψ x • EuclideanSpace.basisFun (Fin d) ℝ r) r < ψ (spatialGraphShear r ψ hψ htrans x) ↔ _
  rw [spatialGraphShear_psi r ψ hψ htrans x]
  simp only [PiLp.add_apply,PiLp.smul_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
  change x r+ψ x < ψ x ↔ x r < 0
  constructor <;> intro h <;> linarith

theorem exists_graphHypograph_dirichlet_H2
    (r : Fin d) (ψ : SpatialCoordinates d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {C : NNReal} (hC : LipschitzWith C ψ)
    (htrans : ∀ (x : SpatialCoordinates d) (t : ℝ), ψ (x+t • EuclideanSpace.basisFun (Fin d) ℝ r)=ψ x)
    {B : Fin d → NNReal} (hB : ∀ i, LipschitzWith (B i) (graphSlopeMultiplier ψ hψ hC i).value)
    (u : WeakSobolevJet d 1 (volume.restrict {x : SpatialCoordinates d | x r < ψ x}) {x | x r < ψ x})
    (hu : u ∈ dirichletJetSpace {x : SpatialCoordinates d | x r < ψ x})
    (f : Lp ℝ 2 (volume.restrict {x : SpatialCoordinates d | x r < ψ x}))
    (hf : IsWeakNegativeLaplacian u f) :
    ∃ U : WeakSobolevJet d 2 (volume.restrict {x : SpatialCoordinates d | x r < ψ x}) {x | x r < ψ x},
      WeakSobolevJet.truncate (by omega : 1 ≤ 2) U=u := by
  have hT : IsOpen {x : SpatialCoordinates d | x r < ψ x} := isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) r) hψ.continuous
  apply exists_dirichlet_H2_of_graph_tangential_invariance hT r ψ hψ hC htrans hB u hu f hf
  rw [spatialGraphShear_hypograph]
  intro j hj t x hx
  have hc : (x+t • EuclideanSpace.basisFun (Fin d) ℝ j) r=x r := by
    simp [EuclideanSpace.basisFun_apply,PiLp.add_apply,PiLp.smul_apply,Ne.symm hj]
  change (x+t • EuclideanSpace.basisFun (Fin d) ℝ j) r < 0 at hx
  change x r < 0
  rwa [hc] at hx

end Carleman
