-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Primitive.gcd_support_reduction
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:13:57.881916+00:00
-- url     : https://prove2.me/submissions/3cd723ba-ae45-4886-ad71-6d1588b586a6

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_coprime_not_both_even
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_nonaffine_iff_gcd
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_coprime
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_modulus_positive
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_patternA_dilate
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_patternB_dilate
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Arithmetic











theorem primitive_parameter_unit (b a : ℕ) (hc : a.Coprime b) (hb : b%4=2) :
    IsUnit (a : ZMod (4*b)) := by
  have hh := coprime_not_both_even a b hc
  have ha : a%2=1 := by omega
  have h2 : a.Coprime 2 := by
    rw [Nat.coprime_two_right]
    exact ⟨a/2,by omega⟩
  apply (ZMod.isUnit_iff_coprime a (4*b)).mpr
  exact (show a.Coprime 4 from by simpa using h2.mul_right h2).mul_right hc

theorem p2m_local_gcd_support_reduction (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (hna : ¬ AffineEquivalent (patternA q x) (patternB q x)) :
    ∃ d b a : ℕ, 0 < d ∧ 0 < b ∧ q=d*b ∧ x.val=d*a ∧ a.Coprime b ∧ b%4=2 ∧
      IsUnit (a : ZMod (4*b)) ∧
      (patternA b (a : ZMod (4*b))).image (dilate (4*q) d)=patternA q x ∧
      (patternB b (a : ZMod (4*b))).image (dilate (4*q) d)=patternB q x := by
  letI : NeZero (4*q) := ⟨by omega⟩
  let d := q.gcd x.val
  let b := q/d
  let a := x.val/d
  have hd : 0 < d := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (by omega))
  have hq' : d*b=q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q x.val)
  have hx' : d*a=x.val := Nat.mul_div_cancel' (Nat.gcd_dvd_right q x.val)
  have hb := reduced_modulus_positive q x.val hq
  have hc := reduced_coprime q x.val hq
  have hm := (nonaffine_iff_gcd q hq x hx).mp hna
  refine ⟨d,b,a,hd,hb,hq'.symm,hx'.symm,hc,hm,primitive_parameter_unit b a hc hm,?_,?_⟩
  · have hh := patternA_dilate d b a hd
    rw [hq',hx',ZMod.natCast_zmod_val] at hh
    exact hh
  · have hh := patternB_dilate d b a hd
    rw [hq',hx',ZMod.natCast_zmod_val] at hh
    exact hh

end Couret.InterIA.Catalogue.Quarter.Primitive

theorem solution : ∀ (q : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
    ∀
      (x :
        ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)),
      Not
          (@Membership.mem.{0, 0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
            (Finset.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
            (@SetLike.instMembership.{0, 0}
              (Finset.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (@Finset.instSetLike.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))))
            (Couret.InterIA.Catalogue.Quarter.badParameters q) x) →
        Not
            (@Couret.InterIA.NormalForm.AffineEquivalent
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
              (Couret.InterIA.Catalogue.Quarter.patternA q x) (Couret.InterIA.Catalogue.Quarter.patternB q x)) →
          @Exists.{1} Nat fun d =>
            @Exists.{1} Nat fun b =>
              @Exists.{1} Nat fun a =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d)
                  (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
                    (And (@Eq.{1} Nat q (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b))
                      (And
                        (@Eq.{1} Nat
                          (@ZMod.val
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
                            x)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d a))
                        (And (Nat.Coprime a b)
                          (And
                            (@Eq.{1} Nat
                              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) b
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (And
                              (@IsUnit.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                (@Semiring.toMonoid.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                  (@CommSemiring.toSemiring.{0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                    (@CommRing.toCommSemiring.{0}
                                      (ZMod
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                      (ZMod.commRing
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b)))))
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
                                  a))
                              (And
                                (@Eq.{1}
                                  (Finset.{0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
                                  (@Finset.image.{0, 0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                                    (ZMod.decidableEq
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                                    (@Couret.InterIA.Catalogue.Quarter.Primitive.dilate
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
                                      d
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                    (Couret.InterIA.Catalogue.Quarter.patternA b
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
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b))))))
                                        a)))
                                  (Couret.InterIA.Catalogue.Quarter.patternA q x))
                                (@Eq.{1}
                                  (Finset.{0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
                                  (@Finset.image.{0, 0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                                    (ZMod.decidableEq
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                                    (@Couret.InterIA.Catalogue.Quarter.Primitive.dilate
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
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
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b))))))
                                        a)))
                                  (Couret.InterIA.Catalogue.Quarter.patternB q x))))))))) := @_root_.Couret.InterIA.Catalogue.Quarter.Primitive.p2m_local_gcd_support_reduction

