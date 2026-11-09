-- Prove2me | solution 1 for Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:32.040438+00:00
-- url     : https://prove2.me/submissions/0de97cb3-4d77-49a1-b360-d3d1358fa5f6

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_numeric
import Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_pos_of_four
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]


















/-- When G has trivial two-torsion, every positive observed fibre has
size one. The order bound ensures that at least one such fibre exists. -/
theorem p2m_local_maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion
    (hh : (twoTorsion : Finset G).card = 1)
    (hn : 4 ≤ Fintype.card G) :
    maxObservedZeroFreeFibreSize (G := G) = 1 := by
  have hExc : (exceptionalFibres : Finset (Finset (Finset G))) = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [exceptionalFibres_card_numeric]
    simp [hh]
  have hObservedExc :
      (zeroFreeExceptionalFibres : Finset (Finset (Finset G))) = ∅ := by
    simp [zeroFreeExceptionalFibres, hExc]
  have hUpper : maxObservedZeroFreeFibreSize (G := G) ≤ 1 := by
    unfold maxObservedZeroFreeFibreSize
    apply Finset.sup_le
    intro F hF
    rw [zeroFreeFullFibres_eq_union, hObservedExc] at hF
    have hOrd : F ∈ (zeroFreeOrdinaryFibres : Finset (Finset (Finset G))) := by
      simpa using hF
    have hb := zeroFreeOrdinaryFibres_card_le_twoTorsion F hOrd
    omega
  have hLower := maxObservedZeroFreeFibreSize_pos_of_four (G := G) hn
  omega























end Couret.STROBO2TORS







universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@Fintype.card.{p2m_u_0} G inst_2) →
      @Eq.{1} Nat (@Couret.STROBO2TORS.maxObservedZeroFreeFibreSize.{p2m_u_0} G inst inst_1 inst_2)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := @_root_.Couret.STROBO2TORS.p2m_local_maxObservedZeroFreeFibreSize_eq_one_of_trivial_two_torsion

