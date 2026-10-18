module

public import Carleman.Spatial.DirichletLaplacian

/-! The full form-operator graph is exactly the distributional negative
divergence of the actual weak gradient on H¹₀, with an L² right side. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def IsWeakNegativeLaplacian (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (f : Lp ℝ 2 (volume.restrict S)) : Prop :=
  ∀ φ : SpatialTest S, weakGradientPairing u φ.sobolevJet = inner ℝ f (φ.toLp (volume.restrict S))

theorem isWeakNegativeLaplacian_iff_dirichlet (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (f : Lp ℝ 2 (volume.restrict S)) :
    IsWeakNegativeLaplacian u f ↔ ∀ v : WeakSobolevJet d 1 (volume.restrict S) S,
      v ∈ dirichletJetSpace S → weakGradientPairing u v = inner ℝ f (WeakSobolevJet.value v) := by
  constructor
  · intro h v hv
    have hc : IsClosed {w : WeakSobolevJet d 1 (volume.restrict S) S |
        weakGradientPairing u w = inner ℝ f (WeakSobolevJet.value w)} :=
      isClosed_eq (weakGradientPairing u).continuous (continuous_const.inner WeakSobolevJet.valueCLM.continuous)
    apply closure_minimal (s := (Submodule.span ℝ (Set.range (fun φ : SpatialTest S => φ.sobolevJet)) : Set _)) _ hc hv
    intro w hw
    obtain ⟨φ,rfl⟩ := exists_test_of_mem_test_span hS hw
    change weakGradientPairing u φ.sobolevJet = inner ℝ f (WeakSobolevJet.value φ.sobolevJet)
    rw [φ.sobolevJet_value]
    exact h φ
  · intro h φ
    simpa only [φ.sobolevJet_value] using h φ.sobolevJet (test_mem_dirichletJetSpace S φ)

theorem negativeLaplacian_isWeak (u : WeakSobolevJet d 2 (volume.restrict S) S) :
    IsWeakNegativeLaplacian (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u) (negativeLaplacian u) :=
  negativeLaplacian_test u

def dirichletJetEnergy (u : WeakSobolevJet d 1 (volume.restrict S) S)
    (hu : u ∈ dirichletJetSpace S) : DirichletEnergy S :=
  ⟨SobolevHilbert.ofJet u,⟨u,hu,rfl⟩⟩

theorem dirichlet_operator_graph_iff (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (x f : Lp ℝ 2 (volume.restrict S)) :
    (∃ z : (boundedDirichletOriginalForm hS hd hb).model.domain,
      (z : Lp ℝ 2 (volume.restrict S)) = x ∧ (boundedDirichletOriginalForm hS hd hb).model.operator z = f) ↔
    ∃ u : WeakSobolevJet d 1 (volume.restrict S) S,
      WeakSobolevJet.value u = x ∧ u ∈ dirichletJetSpace S ∧ IsWeakNegativeLaplacian u f := by
  rw [(boundedDirichletOriginalForm hS hd hb).model.operator_isAssociated x f]
  constructor
  · rintro ⟨v,hv,hf⟩
    refine ⟨SobolevHilbert.toJet v.val,hv,(mem_dirichletJetSpace_iff S hS _).mpr v.property,?_⟩
    intro φ
    have hh := hf (dirichletJetEnergy φ.sobolevJet (test_mem_dirichletJetSpace S φ))
    change weakGradientPairing (SobolevHilbert.toJet v.val) φ.sobolevJet =
      inner ℝ f (WeakSobolevJet.value φ.sobolevJet) at hh
    simpa only [φ.sobolevJet_value] using hh
  · rintro ⟨u,hux,hu,hf⟩
    refine ⟨dirichletJetEnergy u hu,hux,?_⟩
    intro v
    exact (isWeakNegativeLaplacian_iff_dirichlet hS u f).mp hf (SobolevHilbert.toJet v.val)
      ((mem_dirichletJetSpace_iff S hS _).mpr v.property)

end Carleman
