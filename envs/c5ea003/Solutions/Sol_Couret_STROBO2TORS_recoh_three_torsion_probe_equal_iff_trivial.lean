-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_three_torsion_probe_equal_iff_trivial
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:43.380208+00:00
-- url     : https://prove2.me/submissions/844a47c7-db91-463c-ab54-dfa06bd04c79

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



/-- At an order-three point, the condition chi(v)=chi(-v) is
equivalent to triviality of the character at v.
No integral-domain assumption is needed for this implication. -/
theorem p2m_local_recoh_three_torsion_probe_equal_iff_trivial
    {R : Type*} [CommRing R]
    (chi : G → R)
    (hadd : ∀ x y : G, chi (x + y) = chi x * chi y)
    (hzero : chi 0 = 1)
    (v : G) (hv3 : (v + v) + v = 0) :
    (chi v = chi (-v)) ↔ chi v = 1 := by
  constructor
  · intro hequal
    have hinv : chi v * chi (-v) = 1 := by
      calc
        chi v * chi (-v) = chi (v + -v) := (hadd v (-v)).symm
        _ = chi 0 := by rw [add_neg_cancel]
        _ = 1 := hzero
    have hsquare : chi v * chi v = 1 := by
      rw [← hequal] at hinv
      exact hinv
    have hcube : (chi v * chi v) * chi v = 1 := by
      calc
        (chi v * chi v) * chi v = chi (v + v) * chi v := by rw [hadd v v]
        _ = chi ((v + v) + v) := (hadd (v + v) v).symm
        _ = chi 0 := by rw [hv3]
        _ = 1 := hzero
    calc
      chi v = 1 * chi v := by ring
      _ = (chi v * chi v) * chi v := by rw [hsquare]
      _ = 1 := hcube
  · intro hv
    have hinv : chi v * chi (-v) = 1 := by
      calc
        chi v * chi (-v) = chi (v + -v) := (hadd v (-v)).symm
        _ = chi 0 := by rw [add_neg_cancel]
        _ = 1 := hzero
    rw [hv] at hinv
    calc
      chi v = 1 := hv
      _ = chi (-v) := by simpa only [one_mul] using hinv.symm





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
      ∀ (v : G),
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
          Iff
            (@Eq.{p2m_u_1 + 1} R (chi v)
              (chi
                (@Neg.neg.{p2m_u_0} G
                  (@NegZeroClass.toNeg.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                  v)))
            (@Eq.{p2m_u_1 + 1} R (chi v)
              (@OfNat.ofNat.{p2m_u_1} R (nat_lit 1)
                (@One.toOfNat1.{p2m_u_1} R
                  (@AddMonoidWithOne.toOne.{p2m_u_1} R
                    (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_1} R
                      (@Ring.toAddGroupWithOne.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_three_torsion_probe_equal_iff_trivial

