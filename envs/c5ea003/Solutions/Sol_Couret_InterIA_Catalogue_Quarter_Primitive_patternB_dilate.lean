-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Primitive.patternB_dilate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:45:35.74014+00:00
-- url     : https://prove2.me/submissions/fbb11a41-87ed-4804-9b65-4b4b5ab14de9

import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_dilate_nat
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Arithmetic









theorem p2m_local_patternB_dilate (d b a : ℕ) (hd : 0 < d) :
    (patternB b (a : ZMod (4*b))).image (dilate (4*(d*b)) d)=
      patternB (d*b) (d*a : ℕ) := by
  have hz := dilate_nat d b 0 hd
  have hq := dilate_nat d b b hd
  have hx := dilate_nat d b (a+b) hd
  have ht := dilate_nat d b (a+3*b) hd
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_zero] at hz hq hx ht
  simp only [patternB,nsmul_eq_mul,Nat.cast_ofNat,image_insert,image_singleton,hz,hq,hx]
  rw [ht]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_two,Nat.cast_three,mul_zero]
  congr 2 <;> ring





end Couret.InterIA.Catalogue.Quarter.Primitive

theorem solution : ∀ (d b a : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d →
    @Eq.{1}
      (Finset.{0}
        (ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b))))
      (@Finset.image.{0, 0}
        (ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
        (ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)))
        (ZMod.decidableEq
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)))
        (@Couret.InterIA.Catalogue.Quarter.Primitive.dilate
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b))
          d
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
        (Couret.InterIA.Catalogue.Quarter.patternB b
          (@Nat.cast.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
            (@AddMonoidWithOne.toNatCast.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                (@Ring.toAddGroupWithOne.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                  (@CommRing.toRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))))))
            a)))
      (Couret.InterIA.Catalogue.Quarter.patternB (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)
        (@Nat.cast.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)))
          (@AddMonoidWithOne.toNatCast.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)))
            (@AddGroupWithOne.toAddMonoidWithOne.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)))
              (@Ring.toAddGroupWithOne.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)))
                (@CommRing.toRing.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)))
                  (ZMod.commRing
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)))))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d a))) := @_root_.Couret.InterIA.Catalogue.Quarter.Primitive.p2m_local_patternB_dilate

