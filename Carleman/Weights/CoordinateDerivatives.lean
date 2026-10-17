module

public import Carleman.Weights.SpatialDerivatives
public import Carleman.Spatial.SobolevJet
public import Mathlib.Data.Multiset.Sort

/-! Fréchet tensors evaluated on coordinate directions are actual iterated
coordinate derivatives. The derivative collection uses each multi-index once,
in its sorted order, and has the Euclidean norm used in the manuscript. -/
@[expose] public noncomputable section
open Set
open scoped BigOperators ContDiff
namespace Carleman

def coordinateTensorEval {d k : ℕ} (v : Fin k → Fin d) :
    (SpatialCoordinates d [×k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun T => T (fun i => EuclideanSpace.basisFun (Fin d) ℝ (v i))
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
    (SpatialCoordinates d [×k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ).mkContinuous 1 (by
      intro T
      have h := T.le_opNorm (fun i => EuclideanSpace.basisFun (Fin d) ℝ (v i))
      simpa [EuclideanSpace.basisFun_apply] using h)

def coordinateDerivative {d k : ℕ} (v : Fin k → Fin d)
    (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  coordinateTensorEval v (iteratedFDeriv ℝ k f x)

theorem coordinateDerivative_zero {d : ℕ} (v : Fin 0 → Fin d)
    (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) :
    coordinateDerivative v f x = f x := by
  change iteratedFDeriv ℝ 0 f x (fun l => EuclideanSpace.basisFun (Fin d) ℝ (v l)) = f x
  exact iteratedFDeriv_zero_apply _

/-- This recurrence identifies tensor evaluation with repeated coordinate
differentiation, rather than merely naming arbitrary tensor components. -/
theorem coordinateDerivative_cons {d k : ℕ} (v : Fin k → Fin d) (i : Fin d)
    {f : SpatialCoordinates d → ℝ} {x : SpatialCoordinates d}
    (hf : ContDiffAt ℝ (k+1) f x) :
    coordinateDerivative (Fin.cons i v) f x =
      fderiv ℝ (coordinateDerivative v f) x (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  have hd := (coordinateTensorEval v).hasFDerivAt.comp x
    (hf.differentiableAt_iteratedFDeriv (m := k) (by exact_mod_cast Nat.lt_succ_self k)).hasFDerivAt
  change HasFDerivAt (coordinateDerivative v f) _ x at hd
  rw [hd.fderiv]
  change iteratedFDeriv ℝ (k+1) f x
      (fun l : Fin (k+1) => EuclideanSpace.basisFun (Fin d) ℝ (Fin.cons (α := fun _ => Fin d) i v l)) = _
  rw [iteratedFDeriv_succ_apply_left]
  rfl

theorem abs_coordinateDerivative_le {d k : ℕ} (v : Fin k → Fin d)
    (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) :
    |coordinateDerivative v f x| ≤ ‖iteratedFDeriv ℝ k f x‖ := by
  have h := (iteratedFDeriv ℝ k f x).le_opNorm
    (fun l => EuclideanSpace.basisFun (Fin d) ℝ (v l))
  simpa [coordinateDerivative, coordinateTensorEval, EuclideanSpace.basisFun_apply,
    Real.norm_eq_abs] using h

/-- The canonical increasing list contains exactly the given multi-index. -/
def coordinateVector {d k : ℕ} (α : Sym (Fin d) k) : List.Vector (Fin d) k :=
  ⟨(α : Multiset (Fin d)).sort (· ≤ ·), by rw [Multiset.length_sort, Sym.card_coe]⟩

theorem coordinateVector_represents {d k : ℕ} (α : Sym (Fin d) k) :
    Sym.ofVector (coordinateVector α) = α := by
  apply Subtype.ext
  exact Multiset.sort_eq _ _

def coordinateCollection {d k : ℕ} (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) : DerivativeFiber d k :=
  WithLp.toLp 2 (fun α => coordinateDerivative (coordinateVector α).get f x)

/-- The only tensor-to-coordinate loss is the fixed square root of the number
of multi-indices; neither time nor the weight parameters enter it. -/
theorem norm_coordinateCollection_le {d k : ℕ} (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) :
    ‖coordinateCollection (k := k) f x‖ ≤
      Real.sqrt (Fintype.card (Sym (Fin d) k)) * ‖iteratedFDeriv ℝ k f x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _α : Sym (Fin d) k, ‖iteratedFDeriv ℝ k f x‖^2 := by
      apply Finset.sum_le_sum
      intro α _
      change (coordinateDerivative (coordinateVector α).get f x)^2 ≤ _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
        (abs_coordinateDerivative_le (coordinateVector α).get f x)
    _ = _ := by simp

/-- At interior points, the compact-domain within tensor is the actual tensor. -/
theorem iteratedFDerivWithin_eq_of_mem_nhds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} {x : E} (hK : K ∈ nhds x)
    (f : E → ℝ) (k : ℕ) : iteratedFDerivWithin ℝ k f K x = iteratedFDeriv ℝ k f x := by
  rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_congr_set (Filter.eventuallyEqSet_univ.mpr hK) k

/-- All coordinate collections of the allowed positive and inverse weights.
The compact-domain smoothness/unique-differentiation inputs are stated exactly;
the Lipschitz-domain representation is not silently replaced by a stronger domain. -/
theorem allowedWeight_coordinate_derivatives_uniform {d n : ℕ}
    {ρ : SpatialCoordinates d → ℝ} {K : Set (SpatialCoordinates d)}
    (hρ : ContDiffOn ℝ n ρ K) (hK : UniqueDiffOn ℝ K) (hc : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 1 ≤ q → ∀ τ : ℝ, ∀ eta : ℝ, |eta| = 1 →
      ∀ j : ℕ, j ≤ n → ∀ x ∈ interior K,
        ‖coordinateCollection (k := j) (fun y => q^τ * Real.exp (q*(eta*ρ y))) x‖ ≤
          C*q^j*(q^τ * Real.exp (q*(eta*ρ x))) := by
  obtain ⟨C, hC, hb⟩ := allowedWeight_spatial_derivatives_uniform hρ hK hc
  let B : ℝ := 1 + ∑ j : Fin (n+1), Real.sqrt (Fintype.card (Sym (Fin d) j.val))
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B*C, mul_pos hB hC, ?_⟩
  intro q hq τ eta heta j hj x hx
  have hcard : Real.sqrt (Fintype.card (Sym (Fin d) j)) ≤ B := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Fin (n+1) => Real.sqrt (Fintype.card (Sym (Fin d) k.val)))
      (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ (⟨j, by omega⟩ : Fin (n+1)))
    dsimp [B]
    exact hh.trans (by linarith)
  have hh := hb q hq τ eta heta j hj x (interior_subset hx)
  rw [iteratedFDerivWithin_eq_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)] at hh
  calc
    _ ≤ Real.sqrt (Fintype.card (Sym (Fin d) j)) *
        ‖iteratedFDeriv ℝ j (fun y => q^τ * Real.exp (q*(eta*ρ y))) x‖ :=
      norm_coordinateCollection_le _ _
    _ ≤ B * (C*q^j*(q^τ * Real.exp (q*(eta*ρ x)))) := by
      exact mul_le_mul hcard hh (norm_nonneg _) hB.le
    _ = _ := by ring

end Carleman
