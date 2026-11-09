-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_two_torsion_probe_is_sign
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:45.648198+00:00
-- url     : https://prove2.me/submissions/5c3354d6-f9a3-4c3c-ad1b-7dd5de5154e3

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
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH: character masks and genuine translation witnesses.
A dependency of the prospective universal bank bound B(G)=r+s.
No Fourier character-existence or full rank theorem is asserted here.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A normalized multiplicative probe of a two-torsion point is a sign
when its coefficient ring has no zero divisors. -/
theorem p2m_local_recoh_two_torsion_probe_is_sign
    {R : Type*} [CommRing R] [IsDomain R]
    (chi : G → R)
    (hadd : ∀ x y : G, chi (x + y) = chi x * chi y)
    (hzero : chi 0 = 1)
    (d : G) (hd : d + d = 0) :
    chi d = 1 ∨ chi d = -1 := by
  have hmul : chi d * chi d = 1 := by
    calc
      chi d * chi d = chi (d + d) := (hadd d d).symm
      _ = chi 0 := by rw [hd]
      _ = 1 := hzero
  have hfac : (chi d - 1) * (chi d + 1) = 0 := by
    calc
      (chi d - 1) * (chi d + 1) = chi d * chi d - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hmul
  rcases mul_eq_zero.mp hfac with hpos | hneg
  · exact Or.inl (sub_eq_zero.mp hpos)
  · right
    calc
      chi d = (chi d + 1) - 1 := by ring
      _ = -1 := by rw [hneg]; ring







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
    @Eq.{p2m_u_1 + 1} R
        (chi
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
        (@OfNat.ofNat.{p2m_u_1} R (nat_lit 1)
          (@One.toOfNat1.{p2m_u_1} R
            (@AddMonoidWithOne.toOne.{p2m_u_1} R
              (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_1} R
                (@Ring.toAddGroupWithOne.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2)))))) →
      ∀ (d : G),
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
          Or
            (@Eq.{p2m_u_1 + 1} R (chi d)
              (@OfNat.ofNat.{p2m_u_1} R (nat_lit 1)
                (@One.toOfNat1.{p2m_u_1} R
                  (@AddMonoidWithOne.toOne.{p2m_u_1} R
                    (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_1} R
                      (@Ring.toAddGroupWithOne.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2)))))))
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
                        (@Ring.toAddGroupWithOne.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2)))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_two_torsion_probe_is_sign

