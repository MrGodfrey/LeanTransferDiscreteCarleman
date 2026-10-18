module

public import Carleman.Spatial.WeakProjectionResidual
public import Carleman.Spatial.ConformingAllowedInverse
public import Carleman.Weights.FullNodalSuperapproximation

/-! The original projected weighted test superapproximation on the full
Dirichlet P1 space, with the original grading threshold and uniform constants. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

set_option maxHeartbeats 1200000 in
theorem allowed_full_projected_superapproximation
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) (ρ : SpatialProfile (volume.restrict S))
    (hρ : ContDiffOn ℝ 2 ρ.value (closure S))
    (κ c B γ : ℝ) (hκ : 0 < κ) (hcpos : 0 < c) (hBpos : 0 < B)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d)
    [IsFiniteMeasure (volume.restrict S)] :
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ ∃ C > (0:ℝ),
    ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι),
    M.FaceMatching → M.BoundaryFitted →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, 0 < ℓ i) →
      (∀ i, c*M.cellDiameter i ≤ ℓ i) → (∀ i, ℓ i ≤ B*M.cellDiameter i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (w : TimeWeight), M.maxDiameter*w.max ≤ δ →
    ∀ (τ t η : ℝ), |η|=1 →
    ∀ u : WeakSobolevJet d 1 (volume.restrict S) S,
      WeakSobolevJet.value u ∈ M.conformingSpace (dirichletSubspace S) →
    ∃ e : WeakSobolevJet d 1 (volume.restrict S) S,
      let σ := (ρ.scaled η).multiplier w τ t
      let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
      let X := M.conformingSpace (dirichletSubspace S)
      WeakSobolevJet.value e=
        (X.orthogonalProjectionOnto ((σ.mul σ).map (WeakSobolevJet.value u)) : Lp ℝ 2 (volume.restrict S))-
          (σ.mul σ).map (WeakSobolevJet.value u) ∧
      WeakSobolevJet.weightedNorm (w.q t) ξ e ≤
        C*M.maxDiameter*w.max*WeakSobolevJet.weightedNorm (w.q t) σ u := by
  have hρ1 : ContDiffOn ℝ 1 ρ.value (closure S) := hρ.of_le (by norm_num)
  obtain ⟨δ,hδ,hd,Cp,hCp,hproj⟩ := allowed_weight_full_projection hS hc hcompact ρ hρ1 γ hγ hΓ
  obtain ⟨CI,hCI,hinv⟩ := conforming_allowed_weight_inverse hS hc hcompact ρ hρ1 κ B hκ hBpos
  obtain ⟨CE,hCE,hnodal⟩ := allowed_full_nodal_superapproximation hS hc hcompact ρ hρ hκ.le hcpos
  refine ⟨δ,hδ,hd,(2+Cp+CI*Cp)*CE,by positivity,?_⟩
  intro ι _ M hM hB a r ℓ hr hball hshape hℓ hlow hupp hg w hm τ t η hη u hu
  have hsmall : M.maxDiameter*w.q t ≤ 1 := (M.maxDiameter_mul_q_le w hm t).trans hd
  obtain ⟨I,e,hI,he,hgrad,hzero⟩ :=
    hnodal M hM hB w τ t η (w.lower t) hη hsmall a r ℓ hr hball hshape hℓ hlow u hu
  let σ := (ρ.scaled η).multiplier w τ t
  let ξ := (ρ.scaled (-η)).multiplier w (-τ) t
  let X := M.conformingSpace (dirichletSubspace S)
  let pe := X.orthogonalProjectionOnto (WeakSobolevJet.value e)
  obtain ⟨p,hpdir,hp⟩ := (M.conformingSpace_le (dirichletSubspace S)) pe.property
  have hpX : WeakSobolevJet.value p ∈ X := by rw [hp]; exact pe.property
  have hsign : |-η|=1 := by simpa only [abs_neg] using hη
  have hpzero : ξ.seminorm (WeakSobolevJet.value p) ≤ Cp*ξ.seminorm (WeakSobolevJet.value e) := by
    rw [hp]
    exact hproj ι M hM hB ℓ hℓ hg w hm (-τ) t (-η) hsign false (WeakSobolevJet.value e)
  have hpmesh : (M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value p) ≤
      Cp*(M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value e) := by
    rw [hp]
    exact hproj ι M hM hB ℓ hℓ hg w hm (-τ) t (-η) hsign true (WeakSobolevJet.value e)
  have hpinv : ξ.seminorm (WeakSobolevJet.field 1 p) ≤
      CI*(M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value p) :=
    hinv ι M a r ℓ hr hℓ hball hshape hupp w (-τ) t (-η) hsign hsmall (dirichletSubspace S) p hpX
  refine ⟨p-e,?_,?_⟩
  · rw [map_sub,hp]
    exact (projection_error_of_residual X ((σ.mul σ).map (WeakSobolevJet.value u)) I
      (WeakSobolevJet.value e) hI he).symm
  · have hbound := weak_projected_residual_estimate (w.nonneg t) hCI.le ξ (M.inverseWeight ℓ ξ)
      p e hpzero hpmesh hpinv
    let N := WeakSobolevJet.weightedNorm (w.q t) σ u
    have hN : 0 ≤ N := WeakSobolevJet.weightedNorm_nonneg _ _ _
    have hmeshpos : 0 ≤ (M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value e) := apply_nonneg _ _
    have hgradpos : 0 ≤ ξ.seminorm (WeakSobolevJet.field 1 e) := apply_nonneg _ _
    have hfirst : ξ.seminorm (WeakSobolevJet.field 1 e)+CI*Cp*(M.inverseWeight ℓ ξ).seminorm (WeakSobolevJet.value e) ≤
        (1+CI*Cp)*(CE*M.maxDiameter*w.max*N) := by
      have hh := mul_le_mul_of_nonneg_left hgrad (show 0 ≤ 1+CI*Cp by positivity)
      nlinarith [mul_nonneg (mul_nonneg hCI.le hCp.le) hgradpos]
    have hscale : M.maxDiameter^2*w.max^2 ≤ M.maxDiameter*w.max := by
      have hlo := mul_nonneg M.maxDiameter_nonneg (zero_le_one.trans w.max_ge_one)
      have hhi := hm.trans hd
      nlinarith [mul_nonneg hlo (sub_nonneg.mpr hhi)]
    have hzerolinear : w.q t*ξ.seminorm (WeakSobolevJet.value e) ≤ CE*M.maxDiameter*w.max*N := by
      apply hzero.trans
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hCE.le) hN
      convert hh using 1 <;> ring
    have hlast := mul_le_mul_of_nonneg_left hzerolinear (show 0 ≤ 1+Cp by positivity)
    apply hbound.trans
    calc
      _ ≤ (1+CI*Cp)*(CE*M.maxDiameter*w.max*N)+(1+Cp)*(CE*M.maxDiameter*w.max*N) := add_le_add hfirst hlast
      _ = _ := by ring

end Carleman
