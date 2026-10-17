module

public import Carleman.Spatial.SmoothMultipliers
public import Carleman.Spatial.WeightedSobolevNorm

/-! Quantitative high-order Leibniz bounds on genuine L² derivative fields.
All combinatorial losses depend only on the fixed dimension and order. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman

theorem norm_list_sum_le {ι E : Type*} [SeminormedAddCommGroup E] (l : List ι) (f : ι → E) :
    ‖(l.map f).sum‖ ≤ (l.map (fun i => ‖f i‖)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

namespace WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

/-- The actual R-type spatial norm with the parameter factors. -/
def parameterNorm (q : ℝ) (w : BoundedMultiplier ν) (u : WeakSobolevJet d n ν S) : ℝ :=
  ∑ k : Fin (n+1), q^(n-k.val) * w.seminorm (field k u)

theorem parameterNorm_nonneg {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u : WeakSobolevJet d n ν S) : 0 ≤ parameterNorm q w u :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hq _) (apply_nonneg _ _)

theorem parameterNorm_component {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u : WeakSobolevJet d n ν S) (k : Fin (n+1)) :
    q^(n-k.val)*w.seminorm (field k u) ≤ parameterNorm q w u :=
  Finset.single_le_sum (f := fun j : Fin (n+1) => q^(n-j.val)*w.seminorm (field j u))
    (fun _ _ => mul_nonneg (pow_nonneg hq _) (apply_nonneg _ _)) (Finset.mem_univ k)

theorem wordField_weighted_le (w : BoundedMultiplier ν) (u : WeakSobolevJet d n ν S)
    (l : List (Fin d)) (hl : l.length ≤ n) :
    w.seminorm (wordField u l) ≤ w.seminorm (field ⟨l.length, by omega⟩ u) := by
  change ‖w.map (wordField u l)‖ ≤ ‖w.map (field ⟨l.length, by omega⟩ u)‖
  apply Lp.norm_le_norm_of_ae_le
  have he := derivativeComponent_ae (wordIndex l) (field ⟨l.length, by omega⟩ u)
  have he' : wordField u l =ᵐ[ν] (fun x => field ⟨l.length, by omega⟩ u x (wordIndex l)) := by
    rw [wordField, dite_eq_left hl]
    exact he
  filter_upwards [w.map_ae (wordField u l), w.map_ae (field ⟨l.length, by omega⟩ u), he']
    with x h1 h2 hx
  rw [h1, h2, hx, norm_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) (norm_nonneg _)

/-- A single Leibniz term has exactly the original q power after scaling. -/
theorem leibniz_term_bound (a : List (Fin d) → BoundedMultiplier ν) (w : BoundedMultiplier ν)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (ha : ∀ l, l.length ≤ n → ∀ᵐ x ∂ν, |(a l).value x| ≤ C*q^l.length*|w.value x|)
    (u : WeakSobolevJet d n ν S) (l : List (Fin d)) (hl : l.length ≤ n)
    (p : List (Fin d) × List (Fin d)) (hp : p ∈ derivativeSplits l) :
    q^(n-l.length) * ‖(a p.1).map (wordField u p.2)‖ ≤ C*parameterNorm q w u := by
  have hlen := derivativeSplits_lengths l p hp
  have h1 : p.1.length ≤ n := by omega
  have h2 : p.2.length ≤ n := by omega
  have he := (a p.1).seminorm_le_of_weight_le w (C*q^p.1.length) (ha p.1 h1) (wordField u p.2)
  have hw := wordField_weighted_le w u p.2 h2
  have hb := parameterNorm_component hq w u ⟨p.2.length, by omega⟩
  have hpow : q^(n-l.length)*q^p.1.length = q^(n-p.2.length) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ q^(n-l.length)*(C*q^p.1.length*w.seminorm (wordField u p.2)) :=
      mul_le_mul_of_nonneg_left he (pow_nonneg hq _)
    _ ≤ q^(n-l.length)*(C*q^p.1.length*w.seminorm (field ⟨p.2.length, by omega⟩ u)) := by
      gcongr
    _ = C*(q^(n-p.2.length)*w.seminorm (field ⟨p.2.length, by omega⟩ u)) := by
      rw [← hpow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hC

/-- A real norm estimate for the entire expansion, with its 2^k multiplicity. -/
theorem leibnizField_bound (a : List (Fin d) → BoundedMultiplier ν) (w : BoundedMultiplier ν)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (ha : ∀ l, l.length ≤ n → ∀ᵐ x ∂ν, |(a l).value x| ≤ C*q^l.length*|w.value x|)
    (u : WeakSobolevJet d n ν S) (l : List (Fin d)) (hl : l.length ≤ n) :
    q^(n-l.length) * ‖leibnizField a u l‖ ≤ (2:ℝ)^l.length*C*parameterNorm q w u := by
  have hn := norm_list_sum_le (derivativeSplits l) (fun p => (a p.1).map (wordField u p.2))
  have hh := List.sum_le_sum (fun p hp => leibniz_term_bound a w hq hC ha u l hl p hp)
  have hscale : q^(n-l.length) *
      ((derivativeSplits l).map (fun p => ‖(a p.1).map (wordField u p.2)‖)).sum =
      ((derivativeSplits l).map (fun p => q^(n-l.length)*‖(a p.1).map (wordField u p.2)‖)).sum := by
    rw [List.sum_map_mul_left]
  have hconst : ((derivativeSplits l).map (fun _ => C*parameterNorm q w u)).sum =
      (2:ℝ)^l.length*C*parameterNorm q w u := by
    simp [derivativeSplits_length, nsmul_eq_mul, mul_assoc]
  change q^(n-l.length)*‖((derivativeSplits l).map _).sum‖ ≤ _
  exact ((mul_le_mul_of_nonneg_left hn (pow_nonneg hq _)).trans_eq hscale).trans (hh.trans_eq hconst)
end WeakSobolevJet
end Carleman
