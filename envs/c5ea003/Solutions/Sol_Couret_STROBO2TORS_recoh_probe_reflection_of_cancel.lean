-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_probe_reflection_of_cancel
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:53.14461+00:00
-- url     : https://prove2.me/submissions/27251f3d-2739-4086-b170-3b02b3dcb5c4

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
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



/-- A reflection has the same character probe if chi(d)=-1
or chi(v)=chi(-v). No geometric or analytic hypotheses are hidden. -/
theorem p2m_local_recoh_probe_reflection_of_cancel
    {R : Type*} [CommRing R]
    (chi : G → R)
    (hadd : ∀ x y : G, chi (x + y) = chi x * chi y)
    (v d : G) (hc : chi d = -1 ∨ chi v = chi (-v)) :
    recohTripleProbe chi 0 v (v + d) =
      recohTripleProbe chi 0 (-v) ((-v) + d) := by
  unfold recohTripleProbe
  rw [hadd v d, hadd (-v) d]
  rcases hc with hneg | hsame
  · rw [hneg]
    ring
  · rw [hsame]












end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G] {R : Type p2m_u_1}
  [inst_2 : CommRing.{p2m_u_1} R] (chi : G → R),
  (∀ (x y : G),
      @Eq.{p2m_u_1 + 1} R
        (chi
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            x y))
        (@HMul.hMul.{p2m_u_1, p2m_u_1, p2m_u_1} R R R
          (@instHMul.{p2m_u_1} R
            (@Distrib.toMul.{p2m_u_1} R
              (@instDistribOfSemiring.{p2m_u_1} R
                (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)))))
          (chi x) (chi y))) →
    ∀ (v d : G),
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
                v))) →
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
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
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
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              (@Neg.neg.{p2m_u_0} G
                (@NegZeroClass.toNeg.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                v)
              d)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_probe_reflection_of_cancel

