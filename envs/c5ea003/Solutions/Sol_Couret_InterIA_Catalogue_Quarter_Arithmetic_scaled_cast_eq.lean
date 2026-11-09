-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.scaled_cast_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:32:30.476226+00:00
-- url     : https://prove2.me/submissions/7dd832d7-3b4a-4c0d-aed1-3c848fb663e3

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
import Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic



theorem p2m_local_scaled_cast_eq (d n a b : ℕ) (hd : d ≠ 0) :
    ((d*a : ℕ) : ZMod (d*n))=(d*b : ℕ) ↔ (a : ZMod n)=b := by
  rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff]
  exact Nat.ModEq.mul_left_cancel_iff' hd





end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (d n a b : Nat),
  @Ne.{1} Nat d (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    Iff
      (@Eq.{1} (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
        (@Nat.cast.{0} (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
          (@AddMonoidWithOne.toNatCast.{0} (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
            (@AddGroupWithOne.toAddMonoidWithOne.{0}
              (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
              (@Ring.toAddGroupWithOne.{0} (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
                (@CommRing.toRing.{0} (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
                  (ZMod.commRing (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d a))
        (@Nat.cast.{0} (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
          (@AddMonoidWithOne.toNatCast.{0} (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
            (@AddGroupWithOne.toAddMonoidWithOne.{0}
              (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
              (@Ring.toAddGroupWithOne.{0} (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
                (@CommRing.toRing.{0} (ZMod (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))
                  (ZMod.commRing (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d n))))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)))
      (@Eq.{1} (ZMod n)
        (@Nat.cast.{0} (ZMod n)
          (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
              (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
          a)
        (@Nat.cast.{0} (ZMod n)
          (@AddMonoidWithOne.toNatCast.{0} (ZMod n)
            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
              (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
          b)) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_scaled_cast_eq

