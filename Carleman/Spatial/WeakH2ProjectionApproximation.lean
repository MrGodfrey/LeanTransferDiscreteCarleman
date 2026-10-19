module

public import Carleman.Spatial.WeakH2AllowedNodal
public import Carleman.Spatial.MaxDiameterWeight
public import Carleman.Spatial.WeakProjectionResidual

/-! Weighted h² value and h energy approximation for the original L²
projection on the full conforming Dirichlet P1 space. The actual error jet
is chosen once before all allowed weights, times and powers. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

set_option maxHeartbeats 1600000 in
theorem weak_h2_allowed_projection_approximation {d : ℕ} (hdim : d ≤ 3)
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hc : Convex ℝ S)
    (hcompact : IsCompact (closure S)) [IsFiniteMeasure (volume.restrict S)]
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (κ c B γ : ℝ) (hκ : 0 < κ) (hcpos : 0 < c) (hBpos : 0 < B)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit d) :
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ ∃ C > (0:ℝ),
    ∀ (ι : Type*) [Fintype ι] (M : SimplicialPartition S ι),
      M.FaceMatching → M.BoundaryFitted →
    ∀ (a : ι → SpatialCoordinates d) (r ℓ : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) → (∀ i, 0 < ℓ i) →
      (∀ i, c*M.cellDiameter i ≤ ℓ i) → (∀ i, ℓ i ≤ B*M.cellDiameter i) →
      (∀ i j, M.VertexNeighbors i j → ℓ j ≤ γ*ℓ i) →
    ∀ (u : WeakSobolevJet d 2 (volume.restrict S) S),
      WeakSobolevJet.value u ∈ dirichletSubspace S →
    ∃ E : WeakSobolevJet d 1 (volume.restrict S) S, E ∈ dirichletJetSpace S ∧
      WeakSobolevJet.value E=
        ((M.conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto (WeakSobolevJet.value u) :
          Lp ℝ 2 (volume.restrict S))-WeakSobolevJet.value u ∧
    ∀ (w : TimeWeight), M.maxDiameter*w.max ≤ δ →
    ∀ (τ t η : ℝ), |η|=1 →
      let σ := (ρ.scaled η).multiplier w τ t
      σ.seminorm (WeakSobolevJet.value E) ≤ C*M.maxDiameter^2*σ.seminorm (WeakSobolevJet.field 2 u) ∧
      WeakSobolevJet.weightedNorm (w.q t) σ E ≤ C*M.maxDiameter*σ.seminorm (WeakSobolevJet.field 2 u) := by
  obtain ⟨δ,hδ,hδ1,Cp,hCp,hproj⟩ := allowed_weight_full_projection hS hc hcompact ρ hρ γ hγ hΓ
  obtain ⟨CI,hCI,hinv⟩ := conforming_allowed_weight_inverse hS hc hcompact ρ hρ κ B hκ hBpos
  obtain ⟨CE,hCE,hnodal⟩ := weak_h2_allowed_nodal_approximation hdim hS hc hcompact ρ hρ κ c⁻¹ (inv_pos.mpr hcpos)
  let C₀ := (1+Cp)*CE*B^2
  let C₁ := (1+CI*Cp)*CE*B+(1+Cp)*CE*B^2
  let C := 1+C₀+C₁
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨δ,hδ,hδ1,C,hC,?_⟩
  intro ι _ M hM hBnd a r ℓ hr hball hshape hℓ hlow hupp hg u hu
  have hscale (i : ι) : M.cellDiameter i ≤ c⁻¹*ℓ i := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hcpos).mpr (by simpa only [mul_comm] using hlow i)
  obtain ⟨f,e,_,_,_,hI,he,hev,hn⟩ := hnodal ι M hM hBnd a r ℓ hr hℓ hball hshape hscale u hu
  let X := M.conformingSpace (dirichletSubspace S)
  let pe := X.orthogonalProjectionOnto (WeakSobolevJet.value e)
  obtain ⟨p,hpdir,hp⟩ := (M.conformingSpace_le (dirichletSubspace S)) pe.property
  have hpX : WeakSobolevJet.value p ∈ X := by rw [hp]; exact pe.property
  refine ⟨p-e,(dirichletJetSpace S).sub_mem hpdir he,?_,?_⟩
  · rw [map_sub,hp]
    exact (projection_error_of_residual X (WeakSobolevJet.value u) (M.nodalLp hS.measurableSet hM f)
      (WeakSobolevJet.value e) hI hev).symm
  · intro w hm τ t η hη
    let σ := (ρ.scaled η).multiplier w τ t
    let H := σ.seminorm (WeakSobolevJet.field 2 u)
    have hH : 0 ≤ H := apply_nonneg _ _
    have hsmall : M.maxDiameter*w.q t ≤ 1 := (M.maxDiameter_mul_q_le w hm t).trans hδ1
    obtain ⟨hv,hgerr⟩ := hn w τ t η hη hsmall
    have hzero : σ.seminorm (WeakSobolevJet.value e) ≤ CE*B^2*M.maxDiameter^2*H := by
      apply hv.trans
      have hb := mul_le_mul_of_nonneg_left
        (M.cellWeight_mesh_power_le hS hc ℓ (fun i => (hℓ i).le) hBpos.le hupp σ (WeakSobolevJet.field 2 u) 2) hCE.le
      convert hb using 1; ring
    have hgrad : σ.seminorm (WeakSobolevJet.field 1 e)+
        (M.inverseWeight ℓ σ).seminorm (WeakSobolevJet.value e) ≤ CE*B*M.maxDiameter*H := by
      apply hgerr.trans
      have hb := mul_le_mul_of_nonneg_left
        (M.cellWeight_mesh_power_le hS hc ℓ (fun i => (hℓ i).le) hBpos.le hupp σ (WeakSobolevJet.field 2 u) 1) hCE.le
      simpa only [pow_one,mul_assoc] using hb
    have hpzero : σ.seminorm (WeakSobolevJet.value p) ≤ Cp*σ.seminorm (WeakSobolevJet.value e) := by
      rw [hp]
      exact hproj ι M hM hBnd ℓ hℓ hg w hm τ t η hη false (WeakSobolevJet.value e)
    have hpmesh : (M.inverseWeight ℓ σ).seminorm (WeakSobolevJet.value p) ≤
        Cp*(M.inverseWeight ℓ σ).seminorm (WeakSobolevJet.value e) := by
      rw [hp]
      exact hproj ι M hM hBnd ℓ hℓ hg w hm τ t η hη true (WeakSobolevJet.value e)
    have hpinv := hinv ι M a r ℓ hr hℓ hball hshape hupp w τ t η hη hsmall (dirichletSubspace S) p hpX
    have hC0C : C₀ ≤ C := by dsimp only [C]; linarith
    have hC1C : C₁ ≤ C := by dsimp only [C]; linarith
    constructor
    · rw [map_sub]
      calc
        _ ≤ σ.seminorm (WeakSobolevJet.value p)+σ.seminorm (WeakSobolevJet.value e) := map_sub_le_add _ _ _
        _ ≤ (1+Cp)*σ.seminorm (WeakSobolevJet.value e) := by linarith
        _ ≤ (1+Cp)*(CE*B^2*M.maxDiameter^2*H) :=
          mul_le_mul_of_nonneg_left hzero (by positivity)
        _ = C₀*M.maxDiameter^2*H := by dsimp only [C₀]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0C (sq_nonneg _)) hH
    · have hbound := weak_projected_residual_estimate (w.nonneg t) hCI.le σ (M.inverseWeight ℓ σ)
        p e hpzero hpmesh hpinv
      have hfirst : σ.seminorm (WeakSobolevJet.field 1 e)+CI*Cp*(M.inverseWeight ℓ σ).seminorm (WeakSobolevJet.value e) ≤
          (1+CI*Cp)*(CE*B*M.maxDiameter*H) := by
        have hh := mul_le_mul_of_nonneg_left hgrad (show 0 ≤ 1+CI*Cp by positivity)
        have hgp : 0 ≤ σ.seminorm (WeakSobolevJet.field 1 e) := apply_nonneg _ _
        have hip : 0 ≤ (M.inverseWeight ℓ σ).seminorm (WeakSobolevJet.value e) := apply_nonneg _ _
        nlinarith [mul_nonneg (mul_nonneg hCI.le hCp.le) hgp]
      have hqzero : w.q t*σ.seminorm (WeakSobolevJet.value e) ≤ CE*B^2*M.maxDiameter*H := by
        calc
          _ ≤ w.q t*(CE*B^2*M.maxDiameter^2*H) := mul_le_mul_of_nonneg_left hzero (w.nonneg t)
          _ = (M.maxDiameter*w.q t)*(CE*B^2*M.maxDiameter*H) := by ring
          _ ≤ 1*(CE*B^2*M.maxDiameter*H) := mul_le_mul_of_nonneg_right hsmall (by positivity [M.maxDiameter_nonneg])
          _ = _ := one_mul _
      apply hbound.trans
      calc
        _ ≤ (1+CI*Cp)*(CE*B*M.maxDiameter*H)+(1+Cp)*(CE*B^2*M.maxDiameter*H) :=
          add_le_add hfirst (mul_le_mul_of_nonneg_left hqzero (by positivity))
        _ = C₁*M.maxDiameter*H := by dsimp only [C₁]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1C M.maxDiameter_nonneg) hH

end Carleman
