module

public import Carleman.Spatial.DirichletCommutatorIdentity
public import Carleman.Spatial.SobolevTruncation

/-! Relate the actual H¹ Dirichlet commutator fields to the original A2
H²-domain notation. H² membership remains an explicit A1 premise. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem dirichlet_domain_lower_sum (hS : IsOpen S) (hd : 0 < d) (hb : Bornology.IsBounded S)
    (hD : (boundedDirichletOriginalForm hS hd hb).model.domain ≤ sobolevSubspace d 2 (volume.restrict S) S)
    (q : ℝ) (z : (boundedDirichletOriginalForm hS hd hb).model.domain) :
    (∑ k : Fin 2, q^(2-k.val)*‖WeakSobolevJet.field k.castSucc
      (domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z)‖)=
      q^2*‖(z : Lp ℝ 2 (volume.restrict S))‖+
        q*‖WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb z)‖ := by
  let J := domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hD z
  have he : dirichletDomainJet hS hd hb z=WeakSobolevJet.truncate (by decide : 1 ≤ 2) J := by
    apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
    simp only [WeakSobolevJet.truncate_value,dirichletDomainJet_value,J,domainSobolevJet_value]
  have hzero : ‖WeakSobolevJet.field 0 J‖=‖(z : Lp ℝ 2 (volume.restrict S))‖ := by
    have hh := WeakSobolevJet.weighted_zero_eq BoundedMultiplier.one J
    simpa only [BoundedMultiplier.one_seminorm,J,domainSobolevJet_value] using hh
  have hfirst : WeakSobolevJet.field (1 : Fin 2) (dirichletDomainJet hS hd hb z)=
      WeakSobolevJet.field (1 : Fin 3) J := by
    rw [he]
    rfl
  rw [Fin.sum_univ_two]
  norm_num only [Fin.val_zero,Fin.val_one,Nat.sub_zero,Nat.reduceSub,pow_one]
  change q^2*‖WeakSobolevJet.field (0 : Fin 3) J‖+q*‖WeakSobolevJet.field (1 : Fin 3) J‖= _
  rw [hzero,← hfirst]

end Carleman
