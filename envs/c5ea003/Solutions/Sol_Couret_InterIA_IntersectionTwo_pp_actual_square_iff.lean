-- Prove2me | solution 1 for Couret.InterIA.IntersectionTwo.pp_actual_square_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:41.77638+00:00
-- url     : https://prove2.me/submissions/18398756-e555-40c4-a1b8-fd042427aec7

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
import Theorems.Thm_Couret_InterIA_IntersectionTwo_pp_square_iff
import Definitions.Def_Couret_SingleSwap_148f04e2e72b

set_option autoImplicit false
namespace Couret.InterIA.IntersectionTwo
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing
variable {G : Type*} [AddCommGroup G] [DecidableEq G]





















theorem p2m_local_pp_actual_square_iff (C : Finset G) (h : G) (hh : h ≠ 0) (hh2 : h+h=0)
    (a b : G) (ha : Disjoint C (Couret.InterIA.Fibres.fibre h a))
    (hb : Disjoint C (Couret.InterIA.Fibres.fibre h b)) :
    (∀ z, orderedSquare (C ∪ Couret.InterIA.Fibres.fibre h a) z =
      orderedSquare (C ∪ Couret.InterIA.Fibres.fibre h b) z) ↔
      (1+atom h)*(atom a-atom b)*(indicator C+atom a+atom b)=0 := by
  rw [← square_equality_iff,indicator_union_disjoint C _ ha,
    indicator_union_disjoint C _ hb,indicator_fibre h a hh,indicator_fibre h b hh]
  simpa only [pow_two] using pp_square_iff h hh2 (indicator C) a b

end Couret.InterIA.IntersectionTwo

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (C : Finset.{p2m_u_0} G)
  (h : G),
  @Ne.{p2m_u_0 + 1} G h
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
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
      ∀ (a b : G),
        @Disjoint.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.partialOrder.{p2m_u_0} G) (@Finset.instOrderBot.{p2m_u_0} G) C
            (@Couret.InterIA.Fibres.fibre.{p2m_u_0} G inst inst_1 h a) →
          @Disjoint.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.partialOrder.{p2m_u_0} G) (@Finset.instOrderBot.{p2m_u_0} G)
              C (@Couret.InterIA.Fibres.fibre.{p2m_u_0} G inst inst_1 h b) →
            Iff
              (∀ (z : G),
                @Eq.{1} Nat
                  (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
                    (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instUnion.{p2m_u_0} G inst_1) C
                      (@Couret.InterIA.Fibres.fibre.{p2m_u_0} G inst inst_1 h a))
                    z)
                  (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
                    (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instUnion.{p2m_u_0} G inst_1) C
                      (@Couret.InterIA.Fibres.fibre.{p2m_u_0} G inst inst_1 h b))
                    z))
              (@Eq.{p2m_u_0 + 1} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                  (@instHMul.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@AddMonoidAlgebra.instMul.{0, p2m_u_0} Int G Int.instSemiring
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))))
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
                            (@AddGroupWithOne.toAddGroup.{p2m_u_0}
                              (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                              (@Ring.toAddGroupWithOne.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                                (@AddMonoidAlgebra.ring.{0, p2m_u_0} Int G Int.instRing
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))))))
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
                      (@Couret.InterIA.GroupRing.indicator.{p2m_u_0} G C)
                      (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G a))
                    (@Couret.InterIA.IntersectionTwo.atom.{p2m_u_0} G b)))
                (@OfNat.ofNat.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring) (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                    (@MulZeroClass.toZero.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                      (@instMulZeroClassOfSemiring.{p2m_u_0} (@AddMonoidAlgebra.{0, p2m_u_0} Int G Int.instSemiring)
                        (@AddMonoidAlgebra.semiring.{0, p2m_u_0} Int G Int.instSemiring
                          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))))) := @_root_.Couret.InterIA.IntersectionTwo.p2m_local_pp_actual_square_iff

