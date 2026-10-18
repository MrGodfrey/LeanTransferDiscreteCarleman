module

public import Carleman.Spatial.SobolevJet

/-! Linear combinations of genuine weak directional derivatives. The test
function derivative is the actual Fréchet derivative in every direction. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsFiniteMeasureOnCompacts ν]
  {S : Set E}

namespace SpatialTest
variable (φ : SpatialTest S)
theorem derivativeLp_zero : φ.derivativeLp ν (0 : E) = 0 := by
  apply Lp.ext
  filter_upwards [φ.derivativeLp_ae ν 0,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ν)] with x hx hz
  simp only [hx,hz,map_zero,Pi.zero_apply]

theorem derivativeLp_add (e f : E) : φ.derivativeLp ν (e+f) =
    φ.derivativeLp ν e + φ.derivativeLp ν f := by
  apply Lp.ext
  filter_upwards [φ.derivativeLp_ae ν (e+f),φ.derivativeLp_ae ν e,φ.derivativeLp_ae ν f,
    Lp.coeFn_add (φ.derivativeLp ν e) (φ.derivativeLp ν f)] with x he he' hf ha
  simp only [he,ha,Pi.add_apply,he',hf,map_add]

theorem derivativeLp_smul (c : ℝ) (e : E) : φ.derivativeLp ν (c • e) =
    c • φ.derivativeLp ν e := by
  apply Lp.ext
  filter_upwards [φ.derivativeLp_ae ν (c • e),φ.derivativeLp_ae ν e,
    Lp.coeFn_smul c (φ.derivativeLp ν e)] with x he he' hs
  simp only [he,hs,Pi.smul_apply,he',map_smul]
end SpatialTest

namespace IsWeakSpatialDerivative
variable {u v w : Lp ℝ 2 ν} {e f : E}
theorem direction_zero (u : Lp ℝ 2 ν) : IsWeakSpatialDerivative ν S 0 u 0 := by
  intro φ
  simp only [φ.derivativeLp_zero,inner_zero_right,inner_zero_left,neg_zero]

theorem direction_add (h : IsWeakSpatialDerivative ν S e u v)
    (h' : IsWeakSpatialDerivative ν S f u w) : IsWeakSpatialDerivative ν S (e+f) u (v+w) := by
  intro φ
  rw [φ.derivativeLp_add,inner_add_right,inner_add_left,h φ,h' φ]
  ring

theorem direction_smul (h : IsWeakSpatialDerivative ν S e u v) (c : ℝ) :
    IsWeakSpatialDerivative ν S (c • e) u (c • v) := by
  intro φ
  rw [φ.derivativeLp_smul,real_inner_smul_right,real_inner_smul_left,h φ]
  ring

theorem direction_sum {ι : Type*} (s : Finset ι) (e : ι → E) (v : ι → Lp ℝ 2 ν)
    (h : ∀ i ∈ s, IsWeakSpatialDerivative ν S (e i) u (v i)) :
    IsWeakSpatialDerivative ν S (∑ i ∈ s, e i) u (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using direction_zero u
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).direction_add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem sum_states {ι : Type*} (s : Finset ι) (u v : ι → Lp ℝ 2 ν)
    (h : ∀ i ∈ s, IsWeakSpatialDerivative ν S e (u i) (v i)) :
    IsWeakSpatialDerivative ν S e (∑ i ∈ s, u i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (zero (e := e) (ν := ν) (S := S))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end IsWeakSpatialDerivative
end Carleman
