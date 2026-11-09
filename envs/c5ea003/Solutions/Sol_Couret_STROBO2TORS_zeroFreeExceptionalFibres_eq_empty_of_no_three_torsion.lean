-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:46.065275+00:00
-- url     : https://prove2.me/submissions/d672685f-5f85-4907-a3b2-67c2f7b606d1

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_numeric
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

/-- If G has no nonzero 3-torsion, there are no exceptional full
convolution-square fibres, hence no exceptional zero-free fibres. -/
theorem p2m_local_zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion
    (ht : (threeTorsion : Finset G).card = 1) :
    (zeroFreeExceptionalFibres : Finset (Finset (Finset G))) = ∅ := by
  have hZero : (exceptionalFibres : Finset (Finset (Finset G))).card = 0 := by
    rw [exceptionalFibres_card_numeric]
    simp [ht]
  have hEmpty : (exceptionalFibres : Finset (Finset (Finset G))) = ∅ :=
    Finset.card_eq_zero.mp hZero
  simp [zeroFreeExceptionalFibres, hEmpty]


























end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Couret.STROBO2TORS.zeroFreeExceptionalFibres.{p2m_u_0} G inst inst_1 inst_2)
      (@EmptyCollection.emptyCollection.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (@Finset.instEmptyCollection.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeExceptionalFibres_eq_empty_of_no_three_torsion

