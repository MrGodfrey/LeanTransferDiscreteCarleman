module
public import Carleman.Spatial.SubdomainZeroExtension
public import Carleman.Spatial.LpDominatedLimit
/-! The actual restricted load extended by zero converges in the original L² space. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}
  {E : Type*} [NormedAddCommGroup E]

theorem subdomainZeroExtend_restrict_ae (hT : MeasurableSet T) (hTS : T⊆S)
    (f : Lp E 2 (volume.restrict S)) :
    subdomainZeroExtend S hT (subdomainLp hTS f)=ᵐ[volume.restrict S] T.indicator f := by
  have hr := (ae_restrict_iff' hT).mp (subdomainLp_ae hTS f)
  filter_upwards [subdomainZeroExtend_ae hT (subdomainLp hTS f),hr.filter_mono ae_restrict_le]
    with x hx hxf
  rw [hx]
  by_cases ht : x∈T
  · simp only [indicator_of_mem ht,hxf ht]
  · simp only [indicator_of_notMem ht]

theorem subdomainZeroExtend_restrict_tendsto (hS : MeasurableSet S)
    (T : ℕ → Set (SpatialCoordinates d)) (hT : ∀ n, MeasurableSet (T n)) (hTS : ∀ n, T n⊆S)
    (hevent : ∀ x∈S, ∀ᶠ n in atTop, x∈T n) (f : Lp E 2 (volume.restrict S)) :
    Tendsto (fun n => subdomainZeroExtend S (hT n) (subdomainLp (hTS n) f)) atTop (𝓝 f) := by
  have ha (n : ℕ) := subdomainZeroExtend_restrict_ae (hT n) (hTS n) f
  apply lp_two_tendsto_of_dominated_norm_sq _ f (fun x => ‖f x‖^2)
    ((Lp.memLp f).integrable_norm_pow (by decide : 2≠0))
  · intro n
    filter_upwards [ha n] with x hx
    rw [hx]
    by_cases ht : x∈T n
    · simp only [indicator_of_mem ht,sub_self,norm_zero,zero_pow (by decide : 2≠0)]
      exact sq_nonneg _
    · simp only [indicator_of_notMem ht,zero_sub,norm_neg,le_refl]
  · filter_upwards [ae_all_iff.mpr ha,ae_restrict_mem hS] with x hx hxS
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent x hxS] with n hn
    exact ((hx n).trans (indicator_of_mem hn f)).symm

theorem subdomainZeroExtend_restrict_tendsto_of_exhaustion (hS : MeasurableSet S)
    (T : ℕ → Set (SpatialCoordinates d)) (hT : ∀ n, MeasurableSet (T n)) (hTS : ∀ n, T n⊆S)
    (hm : Monotone T) (hcover : S⊆⋃ n, T n) (f : Lp E 2 (volume.restrict S)) :
    Tendsto (fun n => subdomainZeroExtend S (hT n) (subdomainLp (hTS n) f)) atTop (𝓝 f) := by
  apply subdomainZeroExtend_restrict_tendsto hS T hT hTS _ f
  intro x hx
  obtain ⟨N,hN⟩ := mem_iUnion.mp (hcover hx)
  exact eventually_atTop.mpr ⟨N,fun n hn => hm hn hN⟩

end Carleman
