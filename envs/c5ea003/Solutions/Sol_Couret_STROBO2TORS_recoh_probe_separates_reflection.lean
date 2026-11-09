-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_probe_separates_reflection
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:56:20.649101+00:00
-- url     : https://prove2.me/submissions/3dd703bc-6772-4a18-aa79-25f5e0e1744d

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
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











/-- A probe trivial on two-torsion but distinguishing opposite third-order
values separates the two reflected triples, provided 2 is not zero. -/
theorem p2m_local_recoh_probe_separates_reflection
    {R : Type*} [CommRing R] [IsDomain R]
    (chi : G → R)
    (hadd : ∀ x y : G, chi (x + y) = chi x * chi y)
    (v d : G) (hd : chi d = 1)
    (hv : chi v ≠ chi (-v))
    (htwo : (2 : R) ≠ 0) :
    recohTripleProbe chi 0 v (v + d) ≠
      recohTripleProbe chi 0 (-v) (-v + d) := by
  intro heq
  unfold recohTripleProbe at heq
  rw [hadd v d, hadd (-v) d, hd] at heq
  have hzero : (2 : R) * (chi v - chi (-v)) = 0 := by
    calc
      (2 : R) * (chi v - chi (-v)) =
        (chi 0 + chi v + chi v * 1) -
          (chi 0 + chi (-v) + chi (-v) * 1) := by ring
      _ = 0 := sub_eq_zero.mpr heq
  rcases mul_eq_zero.mp hzero with hbad | hbad
  · exact htwo hbad
  · exact hv (sub_eq_zero.mp hbad)

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
    ∀ (v d : G),
      @Eq.{p2m_u_1 + 1} R (chi d)
          (@OfNat.ofNat.{p2m_u_1} R (nat_lit 1)
            (@One.toOfNat1.{p2m_u_1} R
              (@AddMonoidWithOne.toOne.{p2m_u_1} R
                (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_1} R
                  (@Ring.toAddGroupWithOne.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2)))))) →
        @Ne.{p2m_u_1 + 1} R (chi v)
            (chi
              (@Neg.neg.{p2m_u_0} G
                (@NegZeroClass.toNeg.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                v)) →
          @Ne.{p2m_u_1 + 1} R
              (@OfNat.ofNat.{p2m_u_1} R (nat_lit 2)
                (@instOfNatAtLeastTwo.{p2m_u_1} R (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast.{p2m_u_1} R
                    (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_1} R
                      (@Ring.toAddGroupWithOne.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2))))
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@OfNat.ofNat.{p2m_u_1} R (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_1} R
                  (@MulZeroClass.toZero.{p2m_u_1} R
                    (@instMulZeroClassOfSemiring.{p2m_u_1} R
                      (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)))))) →
            @Ne.{p2m_u_1 + 1} R
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
                  d)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_probe_separates_reflection

