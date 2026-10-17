module

import Carleman
import Lean.Util.CollectAxioms

/-! Reject unproved placeholders and new mathematical axioms in the bootstrap result. -/

#check @Carleman.sum_sub_perm
#print axioms Carleman.sum_sub_perm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← collectAxioms ``Carleman.sum_sub_perm do
    unless allowed.contains ax do
      throwError "Carleman.sum_sub_perm depends on an unapproved axiom: {ax}"
