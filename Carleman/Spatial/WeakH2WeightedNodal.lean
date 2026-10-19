module

public import Carleman.Spatial.WeakH2ConformingNodal
public import Carleman.Spatial.WeightedIntegralTransfer
public import Carleman.Spatial.WeightedCellAssembly
public import Carleman.Spatial.SimplicialDiameter

/-! Uniform weighted nodal approximation for every original weak H²∩H¹₀
state. One interpolant and one genuine error jet work for all locally
comparable weights; the right sides retain the actual local mesh size. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem weak_h2_weighted_nodal_approximation (d : ℕ) (hd : d ≤ 3)
    (κ B W : ℝ) (hB : 0 < B) (hW : 0 < W) :
    ∃ C > (0:ℝ), ∀ (ι : Type*) [Fintype ι] (S : Set (SpatialCoordinates d))
      (M : SimplicialPartition S ι) (hS : IsOpen S), Convex ℝ S → Bornology.IsBounded S →
    ∀ [IsFiniteMeasure (volume.restrict S)] (hM : M.FaceMatching), M.BoundaryFitted →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, 0 < ℓ i) →
      (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, M.cellDiameter i ≤ B*ℓ i) →
    ∀ (u : WeakSobolevJet d 2 (volume.restrict S) S),
      WeakSobolevJet.value u ∈ dirichletSubspace S →
    ∃ (f : SpatialCoordinates d → ℝ) (e : WeakSobolevJet d 1 (volume.restrict S) S),
      ContinuousOn f (closure S) ∧ f =ᵐ[volume.restrict S] WeakSobolevJet.value u ∧
      (∀ x ∈ frontier S, f x=0) ∧
      M.nodalLp hS.measurableSet hM f ∈ M.conformingSpace (dirichletSubspace S) ∧
      e ∈ dirichletJetSpace S ∧
      WeakSobolevJet.value e=WeakSobolevJet.value u-M.nodalLp hS.measurableSet hM f ∧
    ∀ (w : BoundedMultiplier (volume.restrict S)) (s : ι → ℝ),
      (∀ i, 0 < s i) →
      (∀ i, ∀ᵐ x ∂volume.restrict (M.cell i), |w.value x| ≤ W*s i ∧ s i ≤ W*|w.value x|) →
      w.seminorm (WeakSobolevJet.value e) ≤
        C*(M.cellWeight (fun i => (ℓ i)^2) w).seminorm (WeakSobolevJet.field 2 u) ∧
      w.seminorm (WeakSobolevJet.field 1 e)+(M.inverseWeight ℓ w).seminorm (WeakSobolevJet.value e) ≤
        C*(M.cellWeight ℓ w).seminorm (WeakSobolevJet.field 2 u) := by
  let A₀ := W^4*16*(tensorCoordinateBound d 2)^2*(d:ℝ)^2*B^4
  let A₁ := W^4*((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*
    (tensorCoordinateBound d 2)^2*(d:ℝ)^2*B^2
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  let C := 1+Real.sqrt A₀+Real.sqrt A₁
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ S M hS hc hb _ hM hBnd a r ℓ hr hℓ hball hshape hscale u hu
  obtain ⟨f,hf,hfu,hzero,hI,e,he,hev,hlocal⟩ :=
    M.exists_weak_h2_conforming_nodal_error hS hc hb hd hM hBnd u hu
  refine ⟨f,e,hf,hfu,hzero,hI,he,hev,?_⟩
  intro w s hs hw
  have hcell (i : ι) := hlocal i (a i) (r i) (M.cellDiameter i) κ (hr i)
    (M.cellDiameter_nonneg i) (hball i) (hshape i) (fun _ hx _ hy => M.dist_le_cellDiameter i hx hy)
  have hvalue (i : ι) : (∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.value e x‖^2) ≤
      A₀*(ℓ i)^4*(∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 2 u x‖^2) := by
    let wi := w.restrictMeasure (M.cell_measure_le_domain hS hc i)
    have ht := wi.integral_transfer_memLp
      (A := 16*(M.cellDiameter i)^4*(tensorCoordinateBound d 2)^2*(d:ℝ)^2)
      hW.le (hs i) (by positivity)
      (hw i) ((Lp.memLp (WeakSobolevJet.value e)).mono_measure (M.cell_measure_le_domain hS hc i))
      ((Lp.memLp (WeakSobolevJet.field 2 u)).mono_measure (M.cell_measure_le_domain hS hc i))
      (by simpa only [Real.norm_eq_abs,sq_abs] using (hcell i).1)
    change (∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.value e x‖^2) ≤ _ at ht
    dsimp only [wi,BoundedMultiplier.restrictMeasure] at ht
    apply ht.trans
    have hi : 0 ≤ ∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 2 u x‖^2 :=
      integral_nonneg fun _ => by positivity
    have hp := pow_le_pow_left₀ (M.cellDiameter_nonneg i) (hscale i) 4
    dsimp only [A₀]
    calc
      _ = (W^4*16*(tensorCoordinateBound d 2)^2*(d:ℝ)^2)*
          (M.cellDiameter i)^4*(∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 2 u x‖^2) := by ring
      _ ≤ (W^4*16*(tensorCoordinateBound d 2)^2*(d:ℝ)^2)*
          (B*ℓ i)^4*(∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 2 u x‖^2) := by gcongr
      _ = _ := by ring
  have hgrad (i : ι) : (∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 1 e x‖^2) ≤
      A₁*(ℓ i)^2*(∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 2 u x‖^2) := by
    let wi := w.restrictMeasure (M.cell_measure_le_domain hS hc i)
    have ht := wi.integral_transfer_memLp
      (A := ((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*
        (M.cellDiameter i)^2*(tensorCoordinateBound d 2)^2*(d:ℝ)^2)
      hW.le (hs i) (by positivity)
      (hw i) ((Lp.memLp (WeakSobolevJet.field 1 e)).mono_measure (M.cell_measure_le_domain hS hc i))
      ((Lp.memLp (WeakSobolevJet.field 2 u)).mono_measure (M.cell_measure_le_domain hS hc i)) (hcell i).2
    change (∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 1 e x‖^2) ≤ _ at ht
    dsimp only [wi,BoundedMultiplier.restrictMeasure] at ht
    apply ht.trans
    have hi : 0 ≤ ∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 2 u x‖^2 :=
      integral_nonneg fun _ => by positivity
    have hp := pow_le_pow_left₀ (M.cellDiameter_nonneg i) (hscale i) 2
    dsimp only [A₁]
    calc
      _ = (W^4*((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*
          (tensorCoordinateBound d 2)^2*(d:ℝ)^2)*(M.cellDiameter i)^2*
          (∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 2 u x‖^2) := by ring
      _ ≤ (W^4*((2:ℝ)^d*(d:ℝ)+128*κ^2*‖derivativeOneFiber (d := d)‖^2)*
          (tensorCoordinateBound d 2)^2*(d:ℝ)^2)*(B*ℓ i)^2*
          (∫ x in M.cell i, |w.value x|^2*‖WeakSobolevJet.field 2 u x‖^2) := by gcongr
      _ = _ := by ring
  have hv := M.weighted_cell_errors_sum hS hc w (WeakSobolevJet.value e) (WeakSobolevJet.field 2 u)
    (fun i => (ℓ i)^2) hA₀ (fun i => by simpa only [← pow_mul] using hvalue i)
  have hg := M.weighted_cell_errors_sum hS hc w (WeakSobolevJet.field 1 e) (WeakSobolevJet.field 2 u) ℓ hA₁ hgrad
  have hi := M.weighted_cell_inverse_errors_sum hS hc w (WeakSobolevJet.value e) (WeakSobolevJet.field 2 u) ℓ hA₀ hvalue
  constructor
  · apply hv.trans
    apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
    dsimp only [C]
    linarith [Real.sqrt_nonneg A₁]
  · have hadd := add_le_add hg hi
    calc
      _ ≤ (Real.sqrt A₀+Real.sqrt A₁)*(M.cellWeight ℓ w).seminorm (WeakSobolevJet.field 2 u) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (apply_nonneg _ _)

end Carleman
