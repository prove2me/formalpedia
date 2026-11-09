-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_probe_separates_translations
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:13.942352+00:00
-- url     : https://prove2.me/submissions/3544de32-ff4f-4e2b-8a21-137ac168ba81

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_probe_translate
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-!
RECOH — bounded rank prerequisites for the universal character-bank claim.
All statements in this module are unconditional Lean theorems, but
they DO NOT yet constitute B(G) = r+s for arbitrary finite abelian G.

We distinguish elementary pigeonhole bounds (arbitrary functions) from the
stronger common two- and three-torsion character-mask construction still outstanding.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]









/-- A single nonzero complex-like character probe separates two translated
triples whenever the character values on the translating elements differ.
The target ring is a domain; no cancellation in an arbitrary ring is assumed. -/
theorem p2m_local_recoh_probe_separates_translations
    {R : Type*} [CommRing R] [IsDomain R]
    (chi : G → R)
    (hadd : ∀ x y : G, chi (x + y) = chi x * chi y)
    (a b c u v : G)
    (hnonzero : recohTripleProbe chi a b c ≠ 0)
    (hseparate : chi u ≠ chi v) :
    recohTripleProbe chi (a + u) (b + u) (c + u) ≠
      recohTripleProbe chi (a + v) (b + v) (c + v) := by
  intro heq
  rw [recoh_triple_probe_translate chi hadd a b c u,
    recoh_triple_probe_translate chi hadd a b c v] at heq
  have hzero : (chi u - chi v) * recohTripleProbe chi a b c = 0 := by
    calc
      (chi u - chi v) * recohTripleProbe chi a b c =
          chi u * recohTripleProbe chi a b c -
            chi v * recohTripleProbe chi a b c := by ring
      _ = 0 := sub_eq_zero.mpr heq
  rcases mul_eq_zero.mp hzero with hdiff | hbase
  · exact hseparate (sub_eq_zero.mp hdiff)
  · exact hnonzero hbase



end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G] {R : Type p2m_u_1}
  [inst_2 : CommRing.{p2m_u_1} R]
  [@IsDomain.{p2m_u_1} R (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2))]
  (chi : G → R),
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
    ∀ (a b c u v : G),
      @Ne.{p2m_u_1 + 1} R (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_1} G R inst_2 chi a b c)
          (@OfNat.ofNat.{p2m_u_1} R (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_1} R
              (@MulZeroClass.toZero.{p2m_u_1} R
                (@instMulZeroClassOfSemiring.{p2m_u_1} R
                  (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)))))) →
        @Ne.{p2m_u_1 + 1} R (chi u) (chi v) →
          @Ne.{p2m_u_1 + 1} R
            (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_1} G R inst_2 chi
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                a u)
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                b u)
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                c u))
            (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_1} G R inst_2 chi
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                a v)
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                b v)
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                c v)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_probe_separates_translations

