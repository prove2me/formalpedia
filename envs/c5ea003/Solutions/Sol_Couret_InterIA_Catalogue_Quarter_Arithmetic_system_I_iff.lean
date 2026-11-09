-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.system_I_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:47:12.75694+00:00
-- url     : https://prove2.me/submissions/6a6be0ff-3c16-45da-ac74-61ba03c99902

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_positive_system_sufficient
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_mod_four
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic





theorem system_I_necessary (b a : ℕ) (hb : 0 < b) (h : System b a 1 1) : b%4=0 := by
  have hh := system_mod_four b a 1 1 hb h
  simp only [one_mul] at hh
  omega















theorem p2m_local_system_I_iff (b a : ℕ) (hb : 0 < b) (hab : a.Coprime b) :
    System b a 1 1 ↔ b%4=0 :=
  ⟨system_I_necessary b a hb,positive_system_sufficient b a 1 hb hab⟩







end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (b a : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
    Nat.Coprime a b →
      Iff
        (Couret.InterIA.Catalogue.Quarter.Arithmetic.System b a
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) b
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_system_I_iff

