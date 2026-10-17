module

public import Carleman.Continuous.FormTimeGraph

/-! The actual V-valued Bochner energy representative of a closed operator
L² graph. The resolvent constructs it and A1 coercivity gives its norm bound. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) {μ : Measure ℝ}

def timeEnergy (u a : Lp H 2 μ) : Lp V 2 μ :=
  (b.resolventEnergy 1 zero_le_one).compLp (a+u)

theorem timeEnergy_ae (u a : Lp H 2 μ) :
    b.timeEnergy u a =ᵐ[μ] (fun t => b.resolventEnergy 1 zero_le_one (a t+u t)) := by
  filter_upwards [(b.resolventEnergy 1 zero_le_one).coeFn_compLp (a+u), Lp.coeFn_add a u]
    with t ht hs
  simpa only [timeEnergy,Pi.add_apply,hs] using ht

/-- This V field embeds to exactly the original H field. -/
theorem timeEnergy_embed {u a : Lp H 2 μ} (hu : (u,a) ∈ b.timeOperatorGraph μ) :
    b.embed.compLp (b.timeEnergy u a) = u := by
  apply Lp.ext
  filter_upwards [b.embed.coeFn_compLp (b.timeEnergy u a),b.timeEnergy_ae u a,
    (b.timeOperatorGraph_ae μ u a).mp hu] with t ht he hg
  rw [ht,he]
  change b.resolventH (a t+u t) = u t
  exact (Set.ext_iff.mp b.operatorGraph_eq (u t,a t)).mp hg

/-- The actual energy integral is the H pairing with the actual operator. -/
theorem timeEnergy_form_ae {u a : Lp H 2 μ} (hu : (u,a) ∈ b.timeOperatorGraph μ) :
    (fun t => b.form (b.timeEnergy u a t) (b.timeEnergy u a t)) =ᵐ[μ]
      (fun t => inner ℝ (u t) (a t)) := by
  filter_upwards [b.timeEnergy_ae u a, (b.timeOperatorGraph_ae μ u a).mp hu] with t he hg
  rw [he,b.resolventEnergy_test]
  have hr : b.embed (b.resolventEnergy 1 zero_le_one (a t+u t)) = u t :=
    (Set.ext_iff.mp b.operatorGraph_eq (u t,a t)).mp hg
  rw [hr,one_smul,add_sub_cancel_right,real_inner_comm]

/-- No elliptic interpolation is used: this is the original A1 form coercivity. -/
theorem timeEnergy_coercive {c : ℝ} (hc : ∀ v : V, c*‖v‖^2 ≤ b.form v v)
    {u a : Lp H 2 μ} (hu : (u,a) ∈ b.timeOperatorGraph μ) :
    c*‖b.timeEnergy u a‖^2 ≤ inner ℝ u a := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def,L2.inner_def,←integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner (b.timeEnergy u a) (b.timeEnergy u a)).const_mul c)
    (L2.integrable_inner u a)
  filter_upwards [b.timeEnergy_form_ae hu] with t ht
  rw [real_inner_self_eq_norm_sq,←ht]
  exact hc _
end Carleman.CoerciveForm
