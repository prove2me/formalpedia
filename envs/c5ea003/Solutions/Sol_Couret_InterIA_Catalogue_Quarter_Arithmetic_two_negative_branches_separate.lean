-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.two_negative_branches_separate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:13.025043+00:00
-- url     : https://prove2.me/submissions/335e4c1c-fcc2-4ca5-9a9e-e70b038b5296

import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_III_gcd_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_IV_gcd_iff
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm





















theorem p2m_local_two_negative_branches_separate : System 6 2 3 2 ∧ ¬ System 6 2 3 0 ∧
    System 6 4 3 0 ∧ ¬ System 6 4 3 2 := by
  simp only [system_IV_gcd_iff 6 2 (by decide),system_III_gcd_iff 6 2 (by decide),
    system_III_gcd_iff 6 4 (by decide),system_IV_gcd_iff 6 4 (by decide)]
  decide

end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : And
  (Couret.InterIA.Catalogue.Quarter.Arithmetic.System (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (And
    (Not
      (Couret.InterIA.Catalogue.Quarter.Arithmetic.System (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (And
      (Couret.InterIA.Catalogue.Quarter.Arithmetic.System (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Not
        (Couret.InterIA.Catalogue.Quarter.Arithmetic.System
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_two_negative_branches_separate

