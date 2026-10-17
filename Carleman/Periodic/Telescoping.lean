module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A finite telescoping identity

Reindexing by a permutation preserves a finite sum. Hence a discrete difference
has zero total over a periodic cycle. This is an auxiliary identity for the
periodic time interfaces in Section 2.4, not the summation-by-parts theorem or
any paper-level Carleman estimate. No time-step or analytic assumptions enter.
-/

public section

namespace Carleman

open scoped BigOperators

/-- A finite difference along any permutation has zero total sum. -/
theorem sum_sub_perm {ι α : Type*} [Fintype ι] [AddCommGroup α]
    (σ : Equiv.Perm ι) (f : ι → α) :
    ∑ i, (f i - f (σ i)) = 0 := by
  rw [Finset.sum_sub_distrib, Equiv.sum_comp σ f, sub_self]

end Carleman

-- Controlled CI probe. This branch must never be merged into main.
namespace Carleman
theorem ci_negative_probe : False := by
  exact True.intro
end Carleman
