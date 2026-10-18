module

public import Carleman.Weights.SquaredWithinDerivatives
public import Carleman.Weights.SpatialComparison

/-! Cell-normalized derivative data for the actual allowed weight squared.
Constants are chosen before the cell, q, exponent, sign, and state. -/
@[expose] public noncomputable section
open Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

theorem allowedSquaredWeight_cell_le (ρ : SpatialCoordinates d → ℝ)
    {q D h τ η : ℝ} (hq : 0 < q) (hD : 0 ≤ D) (hη : |η|=1) (hsmall : h*q ≤ 1)
    {x a : SpatialCoordinates d} (hd : |ρ x-ρ a| ≤ D*h) :
    allowedSquaredWeight ρ q τ η x ≤ Real.exp (2*D)*allowedSquaredWeight ρ q τ η a := by
  have hd' : η*(ρ x-ρ a) ≤ D*h :=
    (le_abs_self _).trans (by simpa only [abs_mul,hη,one_mul] using hd)
  have hm := mul_le_mul_of_nonneg_left hd' hq.le
  have hs := mul_le_mul_of_nonneg_left hsmall hD
  have he : q*(η*(2*ρ x)) ≤ 2*D+q*(η*(2*ρ a)) := by nlinarith only [hm,hs]
  rw [allowedSquaredWeight_eq ρ hq τ η]
  dsimp only
  calc
    _ ≤ q^(2*τ)*Real.exp (2*D+q*(η*(2*ρ a))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.rpow_nonneg hq.le _)
    _ = _ := by rw [Real.exp_add]; ring

theorem allowedSquaredWeight_local_derivative_data
    {S : Set (SpatialCoordinates d)} {ρ : SpatialCoordinates d → ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hρ : ContDiffOn ℝ 2 ρ (closure S)) :
    ∃ C > (0:ℝ), ∀ (T : Affine.Simplex ℝ (SpatialCoordinates d) d),
      simplicialCell T.points ⊆ closure S →
    ∀ q : ℝ, 1 ≤ q → ∀ τ η : ℝ, |η|=1 → ∀ h : ℝ,
      (∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h) → h*q ≤ 1 →
      (∀ x ∈ simplicialCell T.points,
        ‖fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S) x‖ ≤
          C*q*allowedSquaredWeight ρ q τ η (T.points 0)) ∧
      LipschitzOnWith
        (Real.toNNReal (C*q^2*allowedSquaredWeight ρ q τ η (T.points 0)))
        (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S)) (simplicialCell T.points) := by
  have hK := uniqueDiffOn_closure_open_convex hS hc
  obtain ⟨C,hC,hbound⟩ := allowedSquaredWeight_within_derivatives_uniform hρ hK hcompact
  obtain ⟨D,hD,hLip⟩ := smooth_profile_lipschitz hS hc hcompact (hρ.of_le (by norm_num))
  refine ⟨C*Real.exp (2*D),mul_pos hC (Real.exp_pos _),?_⟩
  intro T hT q hq τ η hη h hdiam hsmall
  have hqpos := zero_lt_one.trans_le hq
  have ha : T.points 0 ∈ simplicialCell T.points := subset_convexHull ℝ _ (Set.mem_range_self 0)
  have hcell (x : SpatialCoordinates d) (hx : x ∈ simplicialCell T.points) :
      allowedSquaredWeight ρ q τ η x ≤ Real.exp (2*D)*allowedSquaredWeight ρ q τ η (T.points 0) :=
    allowedSquaredWeight_cell_le ρ hqpos (zero_le_one.trans hD) hη hsmall
      ((hLip x (hT hx) _ (hT ha)).trans (mul_le_mul_of_nonneg_left (hdiam x hx _ ha) (zero_le_one.trans hD)))
  have h1 (x : SpatialCoordinates d) (hx : x ∈ simplicialCell T.points) :
      ‖fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S) x‖ ≤
        (C*Real.exp (2*D))*q*allowedSquaredWeight ρ q τ η (T.points 0) := by
    calc
      _ ≤ C*q*allowedSquaredWeight ρ q τ η x := (hbound q hq τ η hη x (hT hx)).1
      _ ≤ C*q*(Real.exp (2*D)*allowedSquaredWeight ρ q τ η (T.points 0)) :=
        mul_le_mul_of_nonneg_left (hcell x hx) (mul_nonneg hC.le hqpos.le)
      _ = _ := by ring
  refine ⟨h1,?_⟩
  apply derivativeField_lipschitzOn_of_within_bound (simplicialCell_convex T.points) _
    (fderivWithin ℝ (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S)) (closure S))
    (fun x hx => (allowedSquaredWeight_secondWithin hρ hK q τ η (hT hx)).mono hT)
  intro x hx
  rw [Real.coe_toNNReal _ (show 0 ≤ C * Real.exp (2*D) * q^2 *
    allowedSquaredWeight ρ q τ η (T.points 0) by
      dsimp only [allowedSquaredWeight]; positivity)]
  change ‖fderivWithin ℝ (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S)) (closure S) x‖ ≤ _
  calc
    _ ≤ C*q^2*allowedSquaredWeight ρ q τ η x := (hbound q hq τ η hη x (hT hx)).2
    _ ≤ C*q^2*(Real.exp (2*D)*allowedSquaredWeight ρ q τ η (T.points 0)) :=
      mul_le_mul_of_nonneg_left (hcell x hx) (mul_nonneg hC.le (sq_nonneg q))
    _ = _ := by ring

theorem allowedSquaredWeight_multiplier_value {S : Set (SpatialCoordinates d)}
    (ρ : SpatialProfile (MeasureTheory.volume.restrict S)) (w : TimeWeight) (τ t η : ℝ)
    (x : SpatialCoordinates d) :
    allowedSquaredWeight ρ.value (w.q t) τ η x = (((ρ.scaled η).multiplier w τ t).value x)^2 := by
  simp only [allowedSquaredWeight,SpatialProfile.scaled_multiplier_value]
  ring_nf

end Carleman
