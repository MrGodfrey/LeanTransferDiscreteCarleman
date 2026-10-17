module

public import Carleman.Continuous.FormOperator
public import Carleman.Continuous.L2Pairing

/-! The closed associated operator lifts to actual Bochner L² time classes.
The resolvent characterizes its a.e. graph without pointwise domain regularity. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (μ : Measure ℝ)

/-- The defect of the genuine resolvent graph equation in L². -/
def timeGraphDefect : (Lp H 2 μ × Lp H 2 μ) →L[ℝ] Lp H 2 μ :=
  (b.resolventH.compLpL 2 μ).comp
    ((ContinuousLinearMap.snd ℝ (Lp H 2 μ) (Lp H 2 μ)) +
      ContinuousLinearMap.fst ℝ (Lp H 2 μ) (Lp H 2 μ)) -
    ContinuousLinearMap.fst ℝ (Lp H 2 μ) (Lp H 2 μ)

def timeOperatorGraph : Submodule ℝ (Lp H 2 μ × Lp H 2 μ) :=
  (b.timeGraphDefect μ).ker

theorem timeOperatorGraph_mem (u a : Lp H 2 μ) :
    (u,a) ∈ b.timeOperatorGraph μ ↔ (b.resolventH.compLpL 2 μ) (a+u) = u := by
  change _ - u = 0 ↔ _
  exact sub_eq_zero

/-- Strong L² convergence preserves the actual a.e. graph condition. -/
theorem timeOperatorGraph_isClosed :
    IsClosed (b.timeOperatorGraph μ : Set (Lp H 2 μ × Lp H 2 μ)) :=
  (b.timeGraphDefect μ).isClosed_ker

theorem timeOperatorGraph_ae (u a : Lp H 2 μ) :
    (u,a) ∈ b.timeOperatorGraph μ ↔ ∀ᵐ t ∂μ, (u t,a t) ∈ b.operatorGraph := by
  rw [b.timeOperatorGraph_mem]
  have hR := b.resolventH.coeFn_compLp (a+u)
  have ha := Lp.coeFn_add a u
  constructor
  · intro he
    change b.resolventH.compLp (a+u) = u at he
    rw [he] at hR
    filter_upwards [hR, ha] with t ht hat
    change (u t,a t) ∈ (b.operatorGraph : Set (H × H))
    rw [b.operatorGraph_eq]
    change b.resolventH (a t+u t) = u t
    dsimp only [Pi.add_apply] at hat
    rw [hat] at ht
    exact ht.symm
  · intro he
    apply Lp.ext
    filter_upwards [he, hR, ha] with t ht hRt hat
    change (u t,a t) ∈ (b.operatorGraph : Set (H × H)) at ht
    rw [b.operatorGraph_eq] at ht
    change b.resolventH (a t+u t) = u t at ht
    dsimp only [Pi.add_apply] at hat
    exact hRt.trans ((congrArg b.resolventH hat).trans ht)

/-- Any a.e. equal H representative inherits a.e. domain membership and its
actual operator agrees with the prescribed L² class. -/
theorem timeOperatorGraph_representative {u a : Lp H 2 μ}
    (hp : (u,a) ∈ b.timeOperatorGraph μ) (v : ℝ → H) (hv : u =ᵐ[μ] v) :
    (∀ᵐ t ∂μ, v t ∈ b.domain) ∧
    (fun t => b.operator (domainRepresentative b.domain v t)) =ᵐ[μ] a := by
  have hg := (b.timeOperatorGraph_ae μ u a).mp hp
  have he : ∀ᵐ t ∂μ, v t ∈ b.domain ∧
      b.operator (domainRepresentative b.domain v t) = a t := by
    filter_upwards [hg, hv] with t ht hvt
    obtain ⟨w, hw, ha⟩ := (b.operatorGraph_mem (u t) (a t)).mp ht
    have hwv : (w : H) = v t := hw.trans hvt
    have hd : v t ∈ b.domain := hwv ▸ w.property
    refine ⟨hd, ?_⟩
    have hre : domainRepresentative b.domain v t = w := by
      apply Subtype.ext
      simp only [domainRepresentative, dite_eq_left hd]
      exact hwv.symm
    rw [hre, ha]
  exact ⟨he.mono fun _ h => h.1, he.mono fun _ h => h.2⟩

instance timeOperatorGraph_completeSpace [CompleteSpace H] :
    CompleteSpace (b.timeOperatorGraph μ) := by
  let : IsClosed (b.timeOperatorGraph μ : Set (Lp H 2 μ × Lp H 2 μ)) :=
    b.timeOperatorGraph_isClosed μ
  exact IsClosed.completeSpace_coe
end Carleman.CoerciveForm
