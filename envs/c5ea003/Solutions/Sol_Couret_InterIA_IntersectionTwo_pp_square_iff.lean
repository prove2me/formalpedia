-- Prove2me | solution 1 for Couret.InterIA.IntersectionTwo.pp_square_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:33:19.680363+00:00
-- url     : https://prove2.me/submissions/4afb691b-5988-49da-af63-aa065bd99845

import Definitions.Def_Couret_IntersectionTwoAlgebra_ba9c300e13f5
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_L4_normal_form_identity
import Definitions.Def_Couret_SingleSwap_148f04e2e72b

set_option autoImplicit false
namespace Couret.InterIA.IntersectionTwo
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

















/-- The exact P/P residual equation; a necessary and sufficient condition. -/
theorem p2m_local_pp_square_iff (h : G) (hh2 : h+h=0) (c : AddMonoidAlgebra ℤ G) (a b : G) :
    (c+(1+atom h)*atom a)^2 = (c+(1+atom h)*atom b)^2 ↔
      (1+atom h)*(atom a-atom b)*(c+atom a+atom b)=0 := by
  have hH : atom h * atom h = (1 : AddMonoidAlgebra ℤ G) :=
    antipodal_monomial_square h hh2
  have hi : (c+(1+atom h)*atom a)^2-(c+(1+atom h)*atom b)^2 =
      2*((1+atom h)*(atom a-atom b)*(c+atom a+atom b)) := by
    calc
      _ = 2*(1+atom h)*(atom a-atom b)*(c+atom a+atom b) :=
        Couret.InterIA.L4.normal_form_identity (atom h) (atom a) (atom b) c hH
      _ = _ := by ring
  constructor
  · intro he
    apply integer_coefficient_no_two_torsion
    rw [← hi, he, sub_self]
  · intro he
    apply sub_eq_zero.mp
    rw [hi, he, mul_zero]





end Couret.InterIA.IntersectionTwo

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G] (h : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        h h)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    ∀ (c : @AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) (a b : G),
      Iff
        (@Eq.{p2m_u_0 + 1} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
          (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) Nat
            (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
            (@instHPow.{p2m_u_0, 0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) Nat
              (@Monoid.toPow.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@Semiring.toMonoid.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@instHAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@Distrib.toAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@instDistribOfSemiring.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))
              c
              (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@instHMul.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.instMul.{0, p2m_u_0} Int G Int.instSemiring
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))))
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@instHAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@Distrib.toAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                      (@instDistribOfSemiring.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                        (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))
                  (@OfNat.ofNat.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) (nat_lit 1)
                    (@One.toOfNat1.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                      (@AddMonoidAlgebra.zero.{0, p2m_u_0} Int G Int.instSemiring
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G h))
                (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G a)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) Nat
            (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
            (@instHPow.{p2m_u_0, 0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) Nat
              (@Monoid.toPow.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@Semiring.toMonoid.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@instHAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@Distrib.toAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@instDistribOfSemiring.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))
              c
              (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@instHMul.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.instMul.{0, p2m_u_0} Int G Int.instSemiring
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))))
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@instHAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@Distrib.toAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                      (@instDistribOfSemiring.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                        (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))
                  (@OfNat.ofNat.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) (nat_lit 1)
                    (@One.toOfNat1.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                      (@AddMonoidAlgebra.zero.{0, p2m_u_0} Int G Int.instSemiring
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G h))
                (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G b)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@Eq.{p2m_u_0 + 1} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
          (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
            (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
            (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
            (@instHMul.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@AddMonoidAlgebra.instMul.{0, p2m_u_0} Int G Int.instSemiring
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))))
            (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@instHMul.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.instMul.{0, p2m_u_0} Int G Int.instSemiring
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))))
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@instHAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@Distrib.toAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@instDistribOfSemiring.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                      (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))
                (@OfNat.ofNat.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) (nat_lit 1)
                  (@One.toOfNat1.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@AddMonoidAlgebra.zero.{0, p2m_u_0} Int G Int.instSemiring
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G h))
              (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@instHSub.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@SubNegMonoid.toSub.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                      (@AddGroupWithOne.toAddGroup.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                        (@Ring.toAddGroupWithOne.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                          (@AddMonoidAlgebra.ring.{0, p2m_u_0} Int G Int.instRing
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))))
                (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G a)
                (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G b)))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@instHAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@Distrib.toAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@instDistribOfSemiring.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@instHAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@Distrib.toAdd.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@instDistribOfSemiring.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                      (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))
                c (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G a))
              (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G b)))
          (@OfNat.ofNat.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
              (@MulZeroClass.toZero.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@instMulZeroClassOfSemiring.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))))) := @_root_.Couret.InterIA.IntersectionTwo.p2m_local_pp_square_iff

