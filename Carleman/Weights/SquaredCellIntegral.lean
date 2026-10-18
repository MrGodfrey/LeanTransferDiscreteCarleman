module

public import Carleman.Weights.SquaredNodalError
public import Carleman.Spatial.WeightedCellError

/-! Actual local weighted value and gradient errors for σ² times an affine
state, with no pointwise state bound left as a hypothesis. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem allowedSquaredWeight_local_integral_errors
    {S : Set (SpatialCoordinates d)} {ρ : SpatialCoordinates d → ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hρ : ContDiffOn ℝ 2 ρ (closure S)) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C > (0:ℝ), ∀ (T : Affine.Simplex ℝ (SpatialCoordinates d) d),
      simplicialCell T.points ⊆ closure S →
    ∀ q : ℝ, 1 ≤ q → ∀ τ η : ℝ, |η|=1 → ∀ h : ℝ,
      (∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h) → h*q ≤ 1 →
    ∀ (a : SpatialCoordinates d) (r : ℝ), 0 < r →
      Metric.ball a r ⊆ simplicialCell T.points → h ≤ κ*r →
    ∀ p : SpatialCoordinates d →ᵃ[ℝ] ℝ,
      let w := allowedSquaredWeight ρ q τ η
      let I := simplexNodalInterpolant T (fun i => w (T.points i)*p (T.points i))
      let G := affineProductDerivative w (fderivWithin ℝ w (closure S)) p
      let energy := q^4*(∫ x in simplicialCell T.points, w x*(p x)^2)+
        q^2*(∫ x in simplicialCell T.points, w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2)
      (∫ x in simplicialCell T.points, (w x*p x-I x)^2/w x) ≤ C*h^4*energy ∧
      (∫ x in simplicialCell T.points,
        ‖derivativeOneFiber (G x-affineScalarDerivative I)‖^2/w x) ≤ C*h^2*energy := by
  obtain ⟨C₁,hC₁,herror⟩ := allowedSquaredWeight_product_errors hS hc hcompact hρ
  obtain ⟨C₀,hC₀,htransfer⟩ := weighted_cell_error_transfer (d := d)
  obtain ⟨D,hD,hLip⟩ := smooth_profile_lipschitz hS hc hcompact (hρ.of_le (by norm_num))
  let E := Real.exp (2*D)
  let F := ‖derivativeOneFiber (d := d)‖*(1+4*κ)
  have hE : 0 < E := Real.exp_pos _
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨C₀*E^2*C₁^2*(4+F^2),by positivity,?_⟩
  intro T hT q hq τ η hη h hdiam hsmall a r hr hball hshape p
  dsimp only
  let w := allowedSquaredWeight ρ q τ η
  let I := simplexNodalInterpolant T (fun i => w (T.points i)*p (T.points i))
  let G := affineProductDerivative w (fderivWithin ℝ w (closure S)) p
  let b := w (T.points 0)
  let J := q^2*(affineNodalBound T p : ℝ)+2*q*‖affineScalarDerivative p‖
  let energy := q^4*(∫ x in simplicialCell T.points, w x*(p x)^2)+
    q^2*(∫ x in simplicialCell T.points, w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2)
  change (∫ x in simplicialCell T.points, (w x*p x-I x)^2/w x) ≤ _*h^4*energy ∧
    (∫ x in simplicialCell T.points, ‖derivativeOneFiber (G x-affineScalarDerivative I)‖^2/w x) ≤ _*h^2*energy
  have hqpos := zero_lt_one.trans_le hq
  have ha : T.points 0 ∈ simplicialCell T.points := subset_convexHull ℝ _ (Set.mem_range_self 0)
  have hh : 0 ≤ h := (dist_nonneg (x := T.points 0) (y := T.points 0)).trans (hdiam _ ha _ ha)
  have hwpos (x : SpatialCoordinates d) : 0 < w x := by dsimp only [w,allowedSquaredWeight]; positivity
  have hb : 0 < b := hwpos _
  have hw : ContinuousOn w (simplicialCell T.points) :=
    (allowedSquaredWeight_contDiffOn hρ q τ η).continuousOn.mono hT
  have hcomp (x : SpatialCoordinates d) (hx : x ∈ simplicialCell T.points) : b ≤ E*w x :=
    allowedSquaredWeight_cell_le ρ hqpos (zero_le_one.trans hD) hη hsmall
      ((hLip _ (hT ha) x (hT hx)).trans (mul_le_mul_of_nonneg_left (hdiam _ ha x hx) (zero_le_one.trans hD)))
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have henergy : 0 ≤ energy := by
    apply add_nonneg
    · exact mul_nonneg (by positivity) (integral_nonneg (fun x => mul_nonneg (hwpos x).le (sq_nonneg _)))
    · exact mul_nonneg (sq_nonneg q) (integral_nonneg (fun x => mul_nonneg (hwpos x).le (sq_nonneg _)))
  have herrors (x : SpatialCoordinates d) (hx : x ∈ simplicialCell T.points) :=
    herror T hT q hq τ η hη h hdiam hsmall p (affineNodalBound T p)
      (fun y hy => affineNodalBound_abs T p hy) x hx
  have hvalue : (∫ x in simplicialCell T.points, (w x*p x-I x)^2/w x) ≤
      C₀*E^2*(2*C₁*h^2)^2*energy := by
    apply htransfer T p q hqpos.le w (fun x => w x*p x-I x) hw
      ((hw.mul p.continuous_of_finiteDimensional.continuousOn).sub I.continuous_of_finiteDimensional.continuousOn)
      (fun x _ => hwpos x) b E (2*C₁*h^2) hb hE.le (by positivity) hcomp
    intro x hx
    convert (herrors x hx).1 using 1
    ring
  have hW : ContinuousOn (fderivWithin ℝ w (closure S)) (simplicialCell T.points) :=
    (((allowedSquaredWeight_contDiffOn hρ q τ η).fderivWithin
      (uniqueDiffOn_closure_open_convex hS hc) (m := 1) (by norm_num)).continuousOn).mono hT
  have hG : ContinuousOn G (simplicialCell T.points) := by
    exact (hw.smul continuous_const.continuousOn).add
      (p.continuous_of_finiteDimensional.continuousOn.smul hW)
  have hgrad : (∫ x in simplicialCell T.points, ‖derivativeOneFiber (G x-affineScalarDerivative I)‖^2/w x) ≤
      C₀*E^2*(F*C₁*h)^2*energy := by
    have he := htransfer T p q hqpos.le w (fun x => ‖derivativeOneFiber (G x-affineScalarDerivative I)‖) hw
      ((derivativeOneFiber (d := d)).continuous.comp_continuousOn (hG.sub continuous_const.continuousOn)).norm
      (fun x _ => hwpos x) b E (F*C₁*h) hb hE.le (by positivity) hcomp
    apply he
    intro x hx
    rw [abs_of_nonneg (norm_nonneg _)]
    calc
      _ ≤ ‖derivativeOneFiber (d := d)‖*‖G x-affineScalarDerivative I‖ := derivativeOneFiber.le_opNorm _
      _ ≤ ‖derivativeOneFiber (d := d)‖*((1+4*κ)*C₁*b*J*h) :=
        mul_le_mul_of_nonneg_left ((herrors x hx).2 a r κ hr hball hshape) (by positivity)
      _ = _ := by dsimp only [F]; ring
  constructor
  · calc
      _ ≤ C₀*E^2*(2*C₁*h^2)^2*energy := hvalue
      _ ≤ (C₀*E^2*C₁^2*(4+F^2))*h^4*energy := by
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₀.le (sq_nonneg E)) (sq_nonneg C₁))
          (mul_nonneg (sq_nonneg F) (pow_nonneg hh 4))) henergy]
  · calc
      _ ≤ C₀*E^2*(F*C₁*h)^2*energy := hgrad
      _ ≤ (C₀*E^2*C₁^2*(4+F^2))*h^2*energy := by
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC₀.le (sq_nonneg E)) (sq_nonneg C₁))
          (mul_nonneg (sq_nonneg h) henergy)]

end Carleman
