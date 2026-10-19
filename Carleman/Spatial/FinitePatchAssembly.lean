module

public import Carleman.Spatial.L2FiniteOverlap
public import Carleman.Spatial.LocalWeightedNorm
public import Carleman.Geometry.CartesianPatchOverlap

/-! Actual local squared L² estimates assemble globally with only a finite
patch multiplicity loss. Local reconstruction estimates remain explicit. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {ι E F G : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  {S : Set (SpatialCoordinates d)}

theorem finite_patch_h2_assembly
    (A B : ι → Set (SpatialCoordinates d))
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hAS : ∀ i, A i ⊆ S) (hBS : ∀ i, B i ⊆ S)
    (hcover : ∀ᵐ x ∂volume.restrict S, ∃ i, x ∈ A i)
    (M C h : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (hh : 0 ≤ h)
    (hoverlap : ∀ᵐ x ∂volume.restrict S, (finiteCoverMultiplicity B x:ℝ) ≤ M)
    (u : Lp E 2 (volume.restrict S)) (v : Lp F 2 (volume.restrict S))
    (H : Lp G 2 (volume.restrict S))
    (hlocal : ∀ i, ‖subdomainLp (hAS i) u‖+h*‖subdomainLp (hAS i) v‖ ≤
      C*h^2*‖subdomainLp (hBS i) H‖) :
    ‖u‖+h*‖v‖ ≤ Real.sqrt (2*M)*C*h^2*‖H‖ := by
  have hcu := subdomainLp_sq_finite_cover A hA hAS hcover u
  have hcv := subdomainLp_sq_finite_cover A hA hAS hcover v
  have hH := subdomainLp_sq_finite_overlap B hB hBS M hoverlap H
  have hl : ∑ i, (‖subdomainLp (hAS i) u‖^2+h^2*‖subdomainLp (hAS i) v‖^2) ≤
      (C*h^2)^2*∑ i, ‖subdomainLp (hBS i) H‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hp := (sq_le_sq₀ (by positivity) (by positivity)).mpr (hlocal i)
    nlinarith [mul_nonneg (norm_nonneg (subdomainLp (hAS i) u))
      (mul_nonneg hh (norm_nonneg (subdomainLp (hAS i) v)))]
  have ht : ‖u‖^2+h^2*‖v‖^2 ≤ (C*h^2)^2*M*‖H‖^2 := by
    calc
      _ ≤ (∑ i, ‖subdomainLp (hAS i) u‖^2)+h^2*∑ i, ‖subdomainLp (hAS i) v‖^2 :=
        add_le_add hcu (mul_le_mul_of_nonneg_left hcv (sq_nonneg h))
      _ = ∑ i, (‖subdomainLp (hAS i) u‖^2+h^2*‖subdomainLp (hAS i) v‖^2) := by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ (C*h^2)^2*∑ i, ‖subdomainLp (hBS i) H‖^2 := hl
      _ ≤ (C*h^2)^2*(M*‖H‖^2) := mul_le_mul_of_nonneg_left hH (sq_nonneg _)
      _ = _ := by ring
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hM)
  rw [mul_pow,mul_pow,mul_pow,hs]
  nlinarith [sq_nonneg (‖u‖-h*‖v‖)]

theorem weighted_finite_patch_h2_assembly
    (A B : ι → Set (SpatialCoordinates d))
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hAS : ∀ i, A i ⊆ S) (hBS : ∀ i, B i ⊆ S)
    (hcover : ∀ᵐ x ∂volume.restrict S, ∃ i, x ∈ A i)
    (M C h : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (hh : 0 ≤ h)
    (hoverlap : ∀ᵐ x ∂volume.restrict S, (finiteCoverMultiplicity B x:ℝ) ≤ M)
    (w : BoundedMultiplier (volume.restrict S))
    (u : Lp E 2 (volume.restrict S)) (v : Lp F 2 (volume.restrict S))
    (H : Lp G 2 (volume.restrict S))
    (hlocal : ∀ i, (w.onSubdomain (hAS i)).seminorm (subdomainLp (hAS i) u)+
      h*(w.onSubdomain (hAS i)).seminorm (subdomainLp (hAS i) v) ≤
      C*h^2*(w.onSubdomain (hBS i)).seminorm (subdomainLp (hBS i) H)) :
    w.seminorm u+h*w.seminorm v ≤ Real.sqrt (2*M)*C*h^2*w.seminorm H := by
  simp only [BoundedMultiplier.onSubdomain_seminorm] at hlocal
  exact finite_patch_h2_assembly A B hA hB hAS hBS hcover M C h hM hC hh hoverlap
    (w.map u) (w.map v) (w.map H) hlocal

theorem weighted_cartesian_patch_h2_assembly
    (A B : ι → Set (SpatialCoordinates d))
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hAS : ∀ i, A i ⊆ S) (hBS : ∀ i, B i ⊆ S)
    (hcover : ∀ᵐ x ∂volume.restrict S, ∃ i, x ∈ A i)
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (r : ℕ)
    (index : ι → (Fin d → ℤ) × Equiv.Perm (Fin d)) (hinj : Function.Injective index)
    (hpatch : ∀ i, B i ⊆ cartesianPatch o δ r (index i).1)
    (C h : ℝ) (hC : 0 ≤ C) (hh : 0 ≤ h)
    (w : BoundedMultiplier (volume.restrict S))
    (u : Lp E 2 (volume.restrict S)) (v : Lp F 2 (volume.restrict S))
    (H : Lp G 2 (volume.restrict S))
    (hlocal : ∀ i, (w.onSubdomain (hAS i)).seminorm (subdomainLp (hAS i) u)+
      h*(w.onSubdomain (hAS i)).seminorm (subdomainLp (hAS i) v) ≤
      C*h^2*(w.onSubdomain (hBS i)).seminorm (subdomainLp (hBS i) H)) :
    w.seminorm u+h*w.seminorm v ≤
      Real.sqrt (2*((2*r+1)^d*d.factorial:ℕ))*C*h^2*w.seminorm H := by
  apply weighted_finite_patch_h2_assembly A B hA hB hAS hBS hcover
    ((2*r+1)^d*d.factorial:ℕ) C h (by positivity) hC hh ?_ w u v H hlocal
  exact Filter.Eventually.of_forall fun x => by
    exact_mod_cast cartesianPatch_permutation_multiplicity_le o δ hδ r index hinj B hpatch x

end Carleman
