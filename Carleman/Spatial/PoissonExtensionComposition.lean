module

public import Carleman.Spatial.BoxPoissonExtension

/-! Exact composition of actual weak Dirichlet Poisson extensions. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T U : Set (SpatialCoordinates d)}

theorem IsPoissonExtension.refl
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f) :
    IsPoissonExtension Subset.rfl 1 u f u f :=
  ⟨hu,hf,WeakSobolevJet.restrictSubdomain_self u,by simp,by simp,by simp⟩

theorem IsPoissonExtension.trans {hST : S ⊆ T} {hTU : T ⊆ U} {C D : ℝ} (hD : 0 ≤ D)
    {u : WeakSobolevJet d 1 (volume.restrict S) S} {f : Lp ℝ 2 (volume.restrict S)}
    {v : WeakSobolevJet d 1 (volume.restrict T) T} {g : Lp ℝ 2 (volume.restrict T)}
    {w : WeakSobolevJet d 1 (volume.restrict U) U} {h : Lp ℝ 2 (volume.restrict U)}
    (hv : IsPoissonExtension hST C u f v g) (hw : IsPoissonExtension hTU D v g w h) :
    IsPoissonExtension (hST.trans hTU) (D*C) u f w h := by
  rcases hv with ⟨hv0,hvp,hvu,hvf,hvv,hvg⟩
  rcases hw with ⟨hw0,hwp,hwv,hwf,hwvv,hwg⟩
  refine ⟨hw0,hwp,?_,?_,?_,?_⟩
  · rw [← WeakSobolevJet.restrictSubdomain_trans hST hTU,hwv,hvu]
  · exact hwf.trans ((mul_le_mul_of_nonneg_left hvf hD).trans_eq (mul_assoc D C ‖f‖).symm)
  · exact hwvv.trans ((mul_le_mul_of_nonneg_left hvv hD).trans_eq (mul_assoc D C ‖WeakSobolevJet.value u‖).symm)
  · exact hwg.trans ((mul_le_mul_of_nonneg_left hvg hD).trans_eq (mul_assoc D C ‖WeakSobolevJet.field 1 u‖).symm)

end Carleman
