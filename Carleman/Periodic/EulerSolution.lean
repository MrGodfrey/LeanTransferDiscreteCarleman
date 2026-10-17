module

public import Carleman.Periodic.EulerVariational

/-! Actual domain-valued periodic Euler solutions for arbitrary H loads,
constructed from the original coercive form, in both orientations. -/
@[expose] public noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation)

def eulerSolution (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H) : g.Sequence b.domain :=
  fun i => b.domainElement ((b.eulerEnergy g s μ hμ f).ofLp i)
    (f i - s.difference g (fun k => b.embed ((b.eulerEnergy g s μ hμ f).ofLp k)) i -
      μ i • b.embed ((b.eulerEnergy g s μ hμ f).ofLp i)) (b.eulerEnergy_test g s μ hμ f i)

theorem eulerSolution_coe (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H) (i : g.Index) :
    (b.eulerSolution g s μ hμ f i : H) = b.embed ((b.eulerEnergy g s μ hμ f).ofLp i) := rfl

/-- The original space-continuous Euler equation, with the actual cyclic difference. -/
theorem eulerSolution_equation (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H) (i : g.Index) :
    s.difference g (fun k => (b.eulerSolution g s μ hμ f k : H)) i +
      b.operator (b.eulerSolution g s μ hμ f i) + μ i • (b.eulerSolution g s μ hμ f i : H) = f i := by
  simp only [eulerSolution_coe]
  change _ + b.operator (b.domainElement _ _ _) + _ = _
  rw [b.operator_domainElement]
  abel

theorem eulerSolution_unique (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H)
    (v : g.Sequence b.domain)
    (hv : ∀ i, s.difference g (fun k => (v k : H)) i + b.operator (v i) + μ i • (v i : H) = f i) :
    v = b.eulerSolution g s μ hμ f := by
  let U : EulerSpace (V := V) g := WithLp.toLp 2 (fun i => b.energy (v i))
  have he : U = b.eulerEnergy g s μ hμ f := by
    apply variationalSolve_unique (b.eulerForm g s μ) (b.eulerForm_coercive g s μ hμ) (b.eulerLoad g f)
    intro w
    rw [b.eulerForm_apply, b.eulerLoad_apply]
    apply Finset.sum_congr rfl
    intro i _
    change b.form (b.energy (v i)) (w.ofLp i) +
      inner ℝ (s.difference g (fun k => b.embed (b.energy (v k))) i +
        μ i • b.embed (b.energy (v i))) (b.embed (w.ofLp i)) = _
    simp only [b.embed_energy, ← b.operator_test]
    rw [← inner_add_left, ← hv i]
    congr 1
    abel
  funext i
  apply Subtype.ext
  rw [b.eulerSolution_coe, ← he]
  exact (b.embed_energy (v i)).symm

/-- Periodicity is built into the cyclic sequence space, and all loads are
included. This is the existence part of Lemma 3.3, not its weighted estimate. -/
theorem existsUnique_periodicEuler (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H) :
    ∃! v : g.Sequence b.domain,
      ∀ i, s.difference g (fun k => (v k : H)) i + b.operator (v i) + μ i • (v i : H) = f i :=
  ⟨b.eulerSolution g s μ hμ f, b.eulerSolution_equation g s μ hμ f,
    fun v hv => b.eulerSolution_unique g s μ hμ f v hv⟩

end Carleman.CoerciveForm
