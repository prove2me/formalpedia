-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_triple_probe_translate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:27.733062+00:00
-- url     : https://prove2.me/submissions/6ee8e037-8f53-4aa7-a1c9-e481e8eff467

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










/-- Multiplicativity turns a common translation into a common scalar factor
in a three-term character probe. -/
theorem p2m_local_recoh_triple_probe_translate
    {R : Type*} [CommRing R]
    (chi : G → R)
    (hadd : ∀ x y : G, chi (x + y) = chi x * chi y)
    (a b c u : G) :
    recohTripleProbe chi (a + u) (b + u) (c + u) =
      chi u * recohTripleProbe chi a b c := by
  unfold recohTripleProbe
  rw [hadd a u, hadd b u, hadd c u]
  ring





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
    ∀ (a b c u : G),
      @Eq.{p2m_u_1 + 1} R
        (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_1} G R inst_2 chi
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            a u)
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            b u)
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            c u))
        (@HMul.hMul.{p2m_u_1, p2m_u_1, p2m_u_1} R R R
          (@instHMul.{p2m_u_1} R
            (@Distrib.toMul.{p2m_u_1} R
              (@instDistribOfSemiring.{p2m_u_1} R
                (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)))))
          (chi u) (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_1} G R inst_2 chi a b c)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_triple_probe_translate

