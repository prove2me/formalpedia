-- Prove2me | solution 1 for Couret.STROBO2TORS.torsionOrbit_subset_fibre
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:30:55.440798+00:00
-- url     : https://prove2.me/submissions/618f0783-7989-4399-9bb5-92b1337360e2

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]



















theorem p2m_local_torsionOrbit_subset_fibre (S : Finset G) (hS : S.card = 3) :
    torsionOrbit S ⊆ squareFibre S := by
  intro T hT
  obtain ⟨u, hu, ht⟩ := (mem_torsionOrbit S T).mp hT
  apply (mem_squareFibre S T).mpr
  constructor
  · rw [ht, translateSupport_card]; exact hS
  · exact orderedSquare_eq_of_ordinaryPartner S T hS ⟨u, hu, ht⟩






























/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @HasSubset.Subset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.instHasSubset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S)
      (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S) := @_root_.Couret.STROBO2TORS.p2m_local_torsionOrbit_subset_fibre

