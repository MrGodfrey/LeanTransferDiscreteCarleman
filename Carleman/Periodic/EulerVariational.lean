module

public import Carleman.Continuous.FormSolve
public import Carleman.Periodic.Orientation
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Solve the entire periodic backward Euler system by Lax–Milgram on the
finite Hilbert product of the original infinite-dimensional energy space.
No spectral basis, finite-dimensional restriction or solution input is used. -/
@[expose] public noncomputable section
open Set InnerProductSpace
open scoped BigOperators
namespace Carleman
namespace Orientation

def neighbor (s : Orientation) (g : TimeGrid) : g.Index ≃ g.Index :=
  match s with | plus => g.prev | minus => g.next

theorem difference_neighbor (s : Orientation) (g : TimeGrid) {E : Type*}
    [AddCommGroup E] [Module ℝ E] (u : g.Sequence E) (i : g.Index) :
    s.difference g u i = g.dt⁻¹ • (u i - u (s.neighbor g i)) := by cases s <;> rfl

theorem pairing_difference_self_nonneg (s : Orientation) (g : TimeGrid) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u : g.Sequence H) :
    0 ≤ g.pairing (s.difference g u) u := by
  cases s
  · exact g.pairing_dPlus_self_nonneg u
  · exact g.pairing_dMinus_self_nonneg u

end Orientation
namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] (b : CoerciveForm H V)
  (g : TimeGrid) (s : Orientation)

abbrev EulerSpace := PiLp 2 (fun _ : g.Index => V)

def eulerForm (μ : g.Sequence ℝ) : EulerSpace (V := V) g →L[ℝ] EulerSpace (V := V) g →L[ℝ] ℝ :=
  ∑ i : g.Index,
    (b.form.bilinearComp (PiLp.proj 2 (fun _ : g.Index => V) i)
      (PiLp.proj 2 (fun _ : g.Index => V) i) +
    ((innerSL ℝ).bilinearComp
      (g.dt⁻¹ • (b.embed.comp (PiLp.proj 2 (fun _ : g.Index => V) i) -
        b.embed.comp (PiLp.proj 2 (fun _ : g.Index => V) (s.neighbor g i))) +
       μ i • b.embed.comp (PiLp.proj 2 (fun _ : g.Index => V) i))
      (b.embed.comp (PiLp.proj 2 (fun _ : g.Index => V) i)) :
      EulerSpace (V := V) g →L[ℝ] EulerSpace (V := V) g →L[ℝ] ℝ))

theorem eulerForm_apply (μ : g.Sequence ℝ) (u v : EulerSpace (V := V) g) :
    b.eulerForm g s μ u v = ∑ i : g.Index, (b.form (u.ofLp i) (v.ofLp i) +
      inner ℝ (s.difference g (fun k => b.embed (u.ofLp k)) i + μ i • b.embed (u.ofLp i))
        (b.embed (v.ofLp i))) := by
  simp only [eulerForm, sum_apply, add_apply,
    ContinuousLinearMap.bilinearComp_apply, smul_apply, ContinuousLinearMap.comp_apply,
    sub_apply, PiLp.proj_apply, Orientation.difference_neighbor]
  rfl

/-- The cyclic time term is nonnegative; the original A1 coercivity survives
on the whole Hilbert product, uniformly in the number of nodes and dt. -/
theorem eulerForm_coercive (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    IsCoercive (b.eulerForm g s μ) := by
  obtain ⟨c, hc, hb⟩ := b.coercive
  refine ⟨c, hc, ?_⟩
  intro u
  have ht := s.pairing_difference_self_nonneg g (fun i => b.embed (u.ofLp i))
  have ht' : 0 ≤ ∑ i, inner ℝ (s.difference g (fun k => b.embed (u.ofLp k)) i)
      (b.embed (u.ofLp i)) := nonneg_of_mul_nonneg_right ht g.dt_pos
  have hm : 0 ≤ ∑ i, μ i * inner ℝ (b.embed (u.ofLp i)) (b.embed (u.ofLp i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) real_inner_self_nonneg
  have ha := Finset.sum_le_sum (s := Finset.univ) fun i _ => hb (u.ofLp i)
  rw [b.eulerForm_apply]
  simp only [inner_add_left, real_inner_smul_left, Finset.sum_add_distrib]
  have he : c*‖u‖*‖u‖ = ∑ i, c*‖u.ofLp i‖*‖u.ofLp i‖ := by
    simp only [mul_assoc, ← sq, ← Finset.mul_sum, PiLp.norm_sq_eq_of_L2]
  rw [he]
  linarith

def eulerLoad (f : g.Sequence H) : EulerSpace (V := V) g →L[ℝ] ℝ :=
  ∑ i : g.Index, (b.loadFunctional (f i)).comp (PiLp.proj 2 (fun _ : g.Index => V) i)

theorem eulerLoad_apply (f : g.Sequence H) (v : EulerSpace (V := V) g) :
    b.eulerLoad g f v = ∑ i, inner ℝ (f i) (b.embed (v.ofLp i)) := by
  simp only [eulerLoad, sum_apply, ContinuousLinearMap.comp_apply]
  rfl

variable [CompleteSpace V]

def eulerEnergy (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H) : EulerSpace (V := V) g :=
  variationalSolve (b.eulerForm g s μ) (b.eulerForm_coercive g s μ hμ) (b.eulerLoad g f)

/-- Testing at a single node yields the actual nodewise variational equation. -/
theorem eulerEnergy_test (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H)
    (i : g.Index) (w : V) :
    b.form ((b.eulerEnergy g s μ hμ f).ofLp i) w =
      inner ℝ (f i - s.difference g (fun k => b.embed ((b.eulerEnergy g s μ hμ f).ofLp k)) i -
        μ i • b.embed ((b.eulerEnergy g s μ hμ f).ofLp i)) (b.embed w) := by
  have he := variationalSolve_spec (b.eulerForm g s μ) (b.eulerForm_coercive g s μ hμ)
    (b.eulerLoad g f) (PiLp.single 2 i w : EulerSpace (V := V) g)
  change b.eulerForm g s μ (b.eulerEnergy g s μ hμ f) (PiLp.single 2 i w : EulerSpace (V := V) g) = _ at he
  rw [b.eulerForm_apply, b.eulerLoad_apply] at he
  have hsum : ∀ j : g.Index,
      b.form ((b.eulerEnergy g s μ hμ f).ofLp j) ((PiLp.single 2 i w : EulerSpace (V := V) g).ofLp j) +
        inner ℝ (s.difference g (fun k => b.embed ((b.eulerEnergy g s μ hμ f).ofLp k)) j +
          μ j • b.embed ((b.eulerEnergy g s μ hμ f).ofLp j))
          (b.embed ((PiLp.single 2 i w : EulerSpace (V := V) g).ofLp j)) =
      if j = i then b.form ((b.eulerEnergy g s μ hμ f).ofLp i) w +
        inner ℝ (s.difference g (fun k => b.embed ((b.eulerEnergy g s μ hμ f).ofLp k)) i +
          μ i • b.embed ((b.eulerEnergy g s μ hμ f).ofLp i)) (b.embed w) else 0 := by
    intro j
    by_cases hj : j = i
    · subst j; simp only [PiLp.single_apply, ite_true]
    · simp only [PiLp.single_apply, hj, ite_false, map_zero, inner_zero_right, add_zero]
  simp_rw [hsum] at he
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
  have hr : (∑ j : g.Index, inner ℝ (f j) (b.embed ((PiLp.single 2 i w : EulerSpace (V := V) g).ofLp j))) =
      inner ℝ (f i) (b.embed w) := by
    have hh : ∀ j : g.Index, inner ℝ (f j) (b.embed ((PiLp.single 2 i w : EulerSpace (V := V) g).ofLp j)) =
        if j = i then inner ℝ (f i) (b.embed w) else 0 := by
      intro j
      by_cases hj : j = i
      · subst j; simp only [PiLp.single_apply, ite_true]
      · simp only [PiLp.single_apply, hj, ite_false, map_zero, inner_zero_right]
    simp_rw [hh]
    simp
  rw [hr] at he
  simp only [inner_sub_left, inner_add_left] at he ⊢
  linarith

end CoerciveForm
end Carleman
