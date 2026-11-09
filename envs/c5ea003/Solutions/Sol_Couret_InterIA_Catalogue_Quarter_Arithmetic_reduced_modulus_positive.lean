-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.reduced_modulus_positive
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:48.480165+00:00
-- url     : https://prove2.me/submissions/04f7015c-6577-4803-ab14-8d7221dd50f1

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
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm





theorem p2m_local_reduced_modulus_positive (q X : ℕ) (hq : 0 < q) : 0 < q / q.gcd X := by
  have he : q.gcd X*(q/q.gcd X)=q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q X)
  exact Nat.pos_of_mul_pos_left (he.symm ▸ hq)

















end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (q X : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) q (Nat.gcd q X)) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_reduced_modulus_positive

