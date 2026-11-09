-- Prove2me | solution 1 for Couret.STROBO2TORS.threeSignPairs_preimage
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:17.197669+00:00
-- url     : https://prove2.me/submissions/c4e532e0-160a-44db-897a-6d800cb0f646

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]





















































theorem p2m_local_threeSignPairs_preimage (P : Finset G)
    (hP : P ∈ (threeSignPairs : Finset (Finset G))) :
    ((threeTorsion : Finset G).erase 0).filter (fun w => ({w, -w} : Finset G) = P) = P := by
  obtain ⟨v, hv, hp⟩ := Finset.mem_image.mp hP
  have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
  have hv3 := (mem_threeTorsion v).mp (Finset.mem_erase.mp hv).2
  ext w
  constructor
  · intro h
    have hwP := (Finset.mem_filter.mp h).2
    rw [← hwP]; simp
  · intro h
    have hw : w = v ∨ w = -v := by
      rw [← hp] at h
      simpa only [Finset.mem_insert, Finset.mem_singleton] using h
    apply Finset.mem_filter.mpr
    rcases hw with rfl | rfl
    · exact ⟨hv, hp⟩
    · constructor
      · apply Finset.mem_erase.mpr
        exact ⟨neg_ne_zero.mpr hv0, (mem_threeTorsion _).mpr (three_torsion_neg v hv3)⟩
      · rw [← hp]
        simp only [neg_neg]
        exact Finset.pair_comm _ _



































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (P : Finset.{p2m_u_0} G),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
        (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Couret.STROBO2TORS.threeSignPairs.{p2m_u_0} G inst inst_1 inst_2) P →
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
      (@Finset.filter.{p2m_u_0} G
        (fun w =>
          @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) w
              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                (@Neg.neg.{p2m_u_0} G
                  (@NegZeroClass.toNeg.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                  w)))
            P)
        (fun a =>
          @Finset.decidableEq.{p2m_u_0} G inst_1
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                (@Neg.neg.{p2m_u_0} G
                  (@NegZeroClass.toNeg.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                  a)))
            P)
        (@Finset.erase.{p2m_u_0} G inst_1 (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))))
      P := @_root_.Couret.STROBO2TORS.p2m_local_threeSignPairs_preimage

