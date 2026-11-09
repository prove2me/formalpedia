-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.coprime_not_both_even
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:48.252665+00:00
-- url     : https://prove2.me/submissions/aba79bba-392f-4d3c-ae50-e0442ec9c6a4

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
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic















theorem p2m_local_coprime_not_both_even (a b : ℕ) (hab : a.Coprime b) :
    a%2=1 ∨ b%2=1 := by
  by_contra h
  have ha : 2 ∣ a := Nat.dvd_of_mod_eq_zero (by omega)
  have hb : 2 ∣ b := Nat.dvd_of_mod_eq_zero (by omega)
  have hh : 2 ∣ 1 := by simpa only [hab.gcd_eq_one] using Nat.dvd_gcd ha hb
  omega













end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (a b : Nat),
  Nat.Coprime a b →
    Or
      (@Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) a
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) b
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_coprime_not_both_even

