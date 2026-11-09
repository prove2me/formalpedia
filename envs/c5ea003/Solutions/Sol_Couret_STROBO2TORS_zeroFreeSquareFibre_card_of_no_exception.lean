-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeSquareFibre_card_of_no_exception
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:34.298328+00:00
-- url     : https://prove2.me/submissions/8dae7b03-df52-4e28-a3c4-4de00e081739

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_eq_orbit_of_no_exception
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrbit_card
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]













































theorem p2m_local_zeroFreeSquareFibre_card_of_no_exception (S : Finset G) (hS : S.card = 3)
    (hne : ∀ T : Finset G, ¬ ExceptionalPartner S T) :
    (zeroFreeSquareFibre S).card = (twoTorsion : Finset G).card -
      (S ∩ (twoTorsion : Finset G)).card := by
  have heq : zeroFreeSquareFibre S = zeroFreeOrbit S := by
    unfold zeroFreeSquareFibre zeroFreeOrbit
    rw [squareFibre_eq_orbit_of_no_exception S hS hne]
  rw [heq, zeroFreeOrbit_card S hS]




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
    (∀ (T : Finset.{p2m_u_0} G), Not (@Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T)) →
      @Eq.{1} Nat
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.zeroFreeSquareFibre.{p2m_u_0} G inst inst_1 inst_2 S))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@Finset.card.{p2m_u_0} G
            (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S
              (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeSquareFibre_card_of_no_exception

