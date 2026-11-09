-- Prove2me | solution 1 for Couret.STROBO2TORS.mem_exceptionalParams
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:20.212738+00:00
-- url     : https://prove2.me/submissions/0be7893b-6bab-4013-9205-9f8d809a0d28

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]











theorem p2m_local_mem_exceptionalParams (a d v : G) :
    ((a, d), v) ∈ (exceptionalParams : Finset ((G × G) × G)) ↔
      d + d = 0 ∧ d ≠ 0 ∧ (v + v) + v = 0 ∧ v ≠ 0 := by
  simp [exceptionalParams, mem_twoTorsion, mem_threeTorsion, and_comm, and_left_comm, and_assoc]













































































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a d v : G),
  Iff
    (@Membership.mem.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G)
      (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
        (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G))
        (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G)
        (@Finset.instSetLike.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G)))
      (@Couret.STROBO2TORS.exceptionalParams.{p2m_u_0} G inst inst_1 inst_2)
      (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v))
    (And
      (@Eq.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          d d)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
      (And
        (@Ne.{p2m_u_0 + 1} G d
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
        (And
          (@Eq.{p2m_u_0 + 1} G
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                v v)
              v)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
          (@Ne.{p2m_u_0 + 1} G v
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_mem_exceptionalParams

