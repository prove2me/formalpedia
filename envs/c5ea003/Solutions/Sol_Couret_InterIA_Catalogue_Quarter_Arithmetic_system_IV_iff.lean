-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.system_IV_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:47:03.151895+00:00
-- url     : https://prove2.me/submissions/db331272-d01c-43f1-8d52-c15ad7bb0610

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_coprime_not_both_even
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_negative_system_sufficient
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_mod_four
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic











theorem system_IV_necessary (b a : ℕ) (hb : 0 < b) (h : System b a 3 2) : (a+b)%2=0 := by
  have hh := system_mod_four b a 3 2 hb h
  omega















theorem p2m_local_system_IV_iff (b a : ℕ) (hb : 0 < b) (hab : a.Coprime b) :
    System b a 3 2 ↔ (a+b)%2=0 := by
  refine ⟨system_IV_necessary b a hb,fun ha => ?_⟩
  have hh := coprime_not_both_even a b hab
  have hbo : b%2=1 := by omega
  exact negative_system_sufficient b a 2 hb hbo (Or.inr rfl) (by omega)

end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (b a : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
    Nat.Coprime a b →
      Iff
        (Couret.InterIA.Catalogue.Quarter.Arithmetic.System b a
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_system_IV_iff

