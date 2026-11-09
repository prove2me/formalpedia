-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_order_three_reflection_same_square
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:40.653307+00:00
-- url     : https://prove2.me/submissions/e57e37a4-afcb-4d6f-a4ab-3e98d0148fa0

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_reflected_orderedSquare_eq
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH/STROBO Fourier bridge -- bounded formalization layer, 2026-10-14.

This file reuses the already compiled STROBO classification/ordered-square
definitions instead of declaring another square or accepting an unproved
classification. It formalizes the collision witness and the *algebraic*
condition under which one character probe cannot distinguish the pair.

IMPORTANT BOUNDARY:
  * no theorem B(G) = r+s is claimed in this file;
  * the finite-rank/character-existence arguments still need a Lean proof;
  * complex Fourier characters are not assumed merely from ring functions;
  * no analytic, prime-race, novelty or publication claim.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







/-- For a nonzero 2-torsion d and a nonzero 3-torsion v,
the two genuine three-point supports have equal labelled ordered squares.
The equality is an application of the previously certified STROBO
reflection theorem; it does not duplicate the nine-pair classification. -/
theorem p2m_local_recoh_order_three_reflection_same_square
    (v d : G)
    (hv0 : v ≠ 0)
    (hv3 : (v + v) + v = 0)
    (hd0 : d ≠ 0)
    (hd2 : d + d = 0) :
    ∀ z : G,
      orderedSquare ({0, v, v + d} : Finset G) z =
        orderedSquare ({0, -v, -v + d} : Finset G) z := by
  have hv2 : v + v ≠ 0 := by
    intro h2
    have hzero : v = 0 := by
      simpa [h2] using hv3
    exact hv0 hzero
  have hab : (0 : G) + 0 ≠ v + v := by
    simpa using hv2.symm
  have hthree : (((v - (0 : G)) + (v - 0)) + (v - 0)) = 0 := by
    simpa using hv3
  have hneg : v + v - (0 : G) = -v := by
    calc
      v + v - (0 : G) = v + v := by simp
      _ = ((v + v) + v) - v := by abel
      _ = 0 - v := by rw [hv3]
      _ = -v := by simp
  intro z
  have h := reflected_orderedSquare_eq (0 : G) v d hd2 hd0 hab
    (Or.inl hthree) z
  simpa only [hneg] using h








end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (v d : G),
  @Ne.{p2m_u_0 + 1} G v
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
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            v v)
          v)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Ne.{p2m_u_0 + 1} G d
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
              d d)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
          ∀ (z : G),
            @Eq.{1} Nat
              (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) v
                    (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        v d))))
                z)
              (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                    (@Neg.neg.{p2m_u_0} G
                      (@NegZeroClass.toNeg.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                      v)
                    (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        (@Neg.neg.{p2m_u_0} G
                          (@NegZeroClass.toNeg.{p2m_u_0} G
                            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                          v)
                        d))))
                z) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_order_three_reflection_same_square

