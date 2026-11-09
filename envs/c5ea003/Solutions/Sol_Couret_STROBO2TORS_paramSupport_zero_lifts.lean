-- Prove2me | solution 1 for Couret.STROBO2TORS.paramSupport_zero_lifts
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:25.410258+00:00
-- url     : https://prove2.me/submissions/fcf1c2be-67ed-40b1-bedc-90d97ebc8964

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]





















theorem p2m_local_paramSupport_zero_lifts (d v : G) :
    (Finset.univ : Finset G).filter (fun a => 0 ∈ paramSupport ((a, d), v)) =
      (paramSupport ((0, d), v)).image (fun x => -x) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, paramSupport,
    Finset.image_insert, Finset.image_singleton, zero_add, neg_zero,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl (add_eq_zero_iff_eq_neg.mp h.symm))
    · exact Or.inr (Or.inr (add_eq_zero_iff_eq_neg.mp (by simpa [add_assoc] using h.symm)))
  · rintro (h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl (add_eq_zero_iff_eq_neg.mpr h).symm)
    · exact Or.inr (Or.inr (by simpa [add_assoc] using (add_eq_zero_iff_eq_neg.mpr h).symm))

























































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (d v : G),
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
    (@Finset.filter.{p2m_u_0} G
      (fun a =>
        @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
          (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
            (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v))
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
      (fun a =>
        @Finset.decidableMem.{p2m_u_0} G inst_1
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
          (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
            (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v)))
      (@Finset.univ.{p2m_u_0} G inst_2))
    (@Finset.image.{p2m_u_0, p2m_u_0} G G inst_1
      (fun x =>
        @Neg.neg.{p2m_u_0} G
          (@NegZeroClass.toNeg.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
          x)
      (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
        (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
          (@Prod.mk.{p2m_u_0, p2m_u_0} G G
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
            d)
          v))) := @_root_.Couret.STROBO2TORS.p2m_local_paramSupport_zero_lifts

