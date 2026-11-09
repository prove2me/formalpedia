-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_masked_bank_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:12.047677+00:00
-- url     : https://prove2.me/submissions/ac13b1dd-c497-4fe3-9716-583397d76d70

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_order_three_reflection_same_square
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_reflection_of_cancel
import Theorems.Thm_Couret_STROBO2TORS_recoh_reflection_supports_distinct
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














/-- Explicit non-identifiability of a true two-support collision for an
arbitrary finite list of homomorphic probes satisfying the mask.
The existence of a mask for fewer than r+s probes is a SEPARATE theorem. -/
theorem p2m_local_recoh_masked_bank_collision
    {R : Type*} [CommRing R]
    (bank : List (G → R))
    (hadd : ∀ chi ∈ bank, ∀ x y : G, chi (x + y) = chi x * chi y)
    (v d : G) (hv0 : v ≠ 0)
    (hv3 : (v + v) + v = 0)
    (hd0 : d ≠ 0) (hd2 : d + d = 0)
    (hmask : ∀ chi ∈ bank, chi d = -1 ∨ chi v = chi (-v)) :
    (({0, v, v + d} : Finset G) ≠ {0, -v, -v + d}) ∧
      (∀ z : G, orderedSquare ({0, v, v + d} : Finset G) z =
        orderedSquare ({0, -v, -v + d} : Finset G) z) ∧
      (∀ chi ∈ bank, recohTripleProbe chi 0 v (v + d) =
        recohTripleProbe chi 0 (-v) (-v + d)) := by
  refine ⟨recoh_reflection_supports_distinct v d hv0 hv3 hd2,
    recoh_order_three_reflection_same_square v d hv0 hv3 hd0 hd2, ?_⟩
  intro chi hchi
  exact recoh_probe_reflection_of_cancel chi (hadd chi hchi) v d (hmask chi hchi)

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {R : Type p2m_u_1}
  [inst_2 : CommRing.{p2m_u_1} R] (bank : List.{max p2m_u_0 p2m_u_1} (G → R)),
  (∀ (chi : G → R),
      @Membership.mem.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1} (G → R) (List.{max p2m_u_0 p2m_u_1} (G → R))
          (@List.instMembership.{max p2m_u_0 p2m_u_1} (G → R)) bank chi →
        ∀ (x y : G),
          @Eq.{p2m_u_1 + 1} R
            (chi
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                x y))
            (@HMul.hMul.{p2m_u_1, p2m_u_1, p2m_u_1} R R R
              (@instHMul.{p2m_u_1} R
                (@Distrib.toMul.{p2m_u_1} R
                  (@instDistribOfSemiring.{p2m_u_1} R
                    (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)))))
              (chi x) (chi y))) →
    ∀ (v d : G),
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
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  d d)
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
              (∀ (chi : G → R),
                  @Membership.mem.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1} (G → R)
                      (List.{max p2m_u_0 p2m_u_1} (G → R)) (@List.instMembership.{max p2m_u_0 p2m_u_1} (G → R)) bank
                      chi →
                    Or
                      (@Eq.{p2m_u_1 + 1} R (chi d)
                        (@Neg.neg.{p2m_u_1} R
                          (@NegZeroClass.toNeg.{p2m_u_1} R
                            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} R
                              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} R
                                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} R
                                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} R
                                    (@Ring.toAddCommGroup.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2)))))))
                          (@OfNat.ofNat.{p2m_u_1} R (nat_lit 1)
                            (@One.toOfNat1.{p2m_u_1} R
                              (@AddMonoidWithOne.toOne.{p2m_u_1} R
                                (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_1} R
                                  (@Ring.toAddGroupWithOne.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2))))))))
                      (@Eq.{p2m_u_1 + 1} R (chi v)
                        (chi
                          (@Neg.neg.{p2m_u_0} G
                            (@NegZeroClass.toNeg.{p2m_u_0} G
                              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                            v)))) →
                And
                  (@Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                    (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                        (@Zero.toOfNat0.{p2m_u_0} G
                          (@NegZeroClass.toZero.{p2m_u_0} G
                            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                      (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                        v
                        (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                          (@Finset.instSingleton.{p2m_u_0} G)
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            v d))))
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
                        (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                          (@Finset.instSingleton.{p2m_u_0} G)
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
                            d)))))
                  (And
                    (∀ (z : G),
                      @Eq.{1} Nat
                        (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                            (@Finset.instInsert.{p2m_u_0} G inst_1)
                            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                              (@Zero.toOfNat0.{p2m_u_0} G
                                (@NegZeroClass.toZero.{p2m_u_0} G
                                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                              (@Finset.instInsert.{p2m_u_0} G inst_1) v
                              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                (@Finset.instSingleton.{p2m_u_0} G)
                                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                  (@instHAdd.{p2m_u_0} G
                                    (@AddCommMagma.toAdd.{p2m_u_0} G
                                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                  v d))))
                          z)
                        (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                            (@Finset.instInsert.{p2m_u_0} G inst_1)
                            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                              (@Zero.toOfNat0.{p2m_u_0} G
                                (@NegZeroClass.toZero.{p2m_u_0} G
                                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                              (@Finset.instInsert.{p2m_u_0} G inst_1)
                              (@Neg.neg.{p2m_u_0} G
                                (@NegZeroClass.toNeg.{p2m_u_0} G
                                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                                v)
                              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                                (@Finset.instSingleton.{p2m_u_0} G)
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
                          z))
                    (∀ (chi : G → R),
                      @Membership.mem.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1} (G → R)
                          (List.{max p2m_u_0 p2m_u_1} (G → R)) (@List.instMembership.{max p2m_u_0 p2m_u_1} (G → R)) bank
                          chi →
                        @Eq.{p2m_u_1 + 1} R
                          (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_1} G R inst_2 chi
                            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                              (@Zero.toOfNat0.{p2m_u_0} G
                                (@NegZeroClass.toZero.{p2m_u_0} G
                                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                            v
                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                              (@instHAdd.{p2m_u_0} G
                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                              v d))
                          (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_1} G R inst_2 chi
                            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                              (@Zero.toOfNat0.{p2m_u_0} G
                                (@NegZeroClass.toZero.{p2m_u_0} G
                                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                            (@Neg.neg.{p2m_u_0} G
                              (@NegZeroClass.toNeg.{p2m_u_0} G
                                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                              v)
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
                              d)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_masked_bank_collision

