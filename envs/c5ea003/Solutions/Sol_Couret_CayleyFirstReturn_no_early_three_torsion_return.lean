-- Prove2me | solution 1 for Couret.CayleyFirstReturn.no_early_three_torsion_return
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:23.222193+00:00
-- url     : https://prove2.me/submissions/dffa5fea-ec83-476e-a2da-fd464312ca7c

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 — separation before the canonical third-period (18 October 2026).

RESEARCH PROOF CANDIDATES — NOT YET COMPILED.

This module separates two logically different tasks:
(1) if the image of a has order 3*ell and 3*delta=0, then no positive
    j<ell can reach +delta or -delta; this needs no cyclic classification;
(2) the quotient application transfers this fact into equality of the
    directed adjacency-matrix traces at EVERY degree strictly below ell.

It does NOT prove that ell*a is +delta or -delta: the canonical RETURN
theorem is still a distinct open Lean obligation. It also does NOT prove
the universal Newton identity needed for characteristic coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyFirstReturn

/-- There cannot be an early return to a three-torsion class.
The only arithmetic input is that the order of alpha is 3*ell:
a hypothetical return at j forces (3*ell) | (3*j), contradicting
0 < j < ell. The result is even stronger than the needed odd case. -/
theorem p2m_local_no_early_three_torsion_return
    {Q : Type*} [AddGroup Q] (alpha delta : Q) (ell j : ℕ)
    (hord : addOrderOf alpha = 3 * ell)
    (hthree : (3 : ℕ) • delta = 0)
    (hjpos : 0 < j) (hjlt : j < ell) :
    j • alpha ≠ delta ∧ j • alpha ≠ -delta := by
  have hbad (hreturn : j • alpha = delta ∨ j • alpha = -delta) : False := by
    have hzero : (3 * j) • alpha = 0 := by
      rw [mul_nsmul']
      rcases hreturn with hplus | hminus
      · rw [hplus, hthree]
      · rw [hminus]
        simp [hthree]
    have hdiv : addOrderOf alpha ∣ 3 * j :=
      (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hzero
    have hle : 3 * ell ≤ 3 * j := by
      rw [← hord]
      exact Nat.le_of_dvd (by omega) hdiv
    omega
  exact ⟨fun hp => hbad (Or.inl hp), fun hm => hbad (Or.inr hm)⟩

end Couret.CayleyFirstReturn

namespace Couret.CayleyDoublet

open Couret.CayleyFirstReturn

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]







end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {Q : Type p2m_u_0} [inst : AddGroup.{p2m_u_0} Q] (alpha delta : Q) (ell j : Nat),
  @Eq.{1} Nat
      (@addOrderOf.{p2m_u_0} Q (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q (@AddGroup.toSubNegMonoid.{p2m_u_0} Q inst))
        alpha)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell) →
    @Eq.{p2m_u_0 + 1} Q
        (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
          (@instHSMul.{0, p2m_u_0} Nat Q
            (@AddMonoid.toNSMul.{p2m_u_0} Q
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q (@AddGroup.toSubNegMonoid.{p2m_u_0} Q inst))))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) delta)
        (@OfNat.ofNat.{p2m_u_0} Q (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} Q
            (@NegZeroClass.toZero.{p2m_u_0} Q
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} Q
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} Q
                  (@AddGroup.toSubtractionMonoid.{p2m_u_0} Q inst)))))) →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
        @LT.lt.{0} Nat instLTNat j ell →
          And
            (@Ne.{p2m_u_0 + 1} Q
              (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
                (@instHSMul.{0, p2m_u_0} Nat Q
                  (@AddMonoid.toNSMul.{p2m_u_0} Q
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q (@AddGroup.toSubNegMonoid.{p2m_u_0} Q inst))))
                j alpha)
              delta)
            (@Ne.{p2m_u_0 + 1} Q
              (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
                (@instHSMul.{0, p2m_u_0} Nat Q
                  (@AddMonoid.toNSMul.{p2m_u_0} Q
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q (@AddGroup.toSubNegMonoid.{p2m_u_0} Q inst))))
                j alpha)
              (@Neg.neg.{p2m_u_0} Q
                (@NegZeroClass.toNeg.{p2m_u_0} Q
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} Q
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} Q
                      (@AddGroup.toSubtractionMonoid.{p2m_u_0} Q inst))))
                delta)) := @_root_.Couret.CayleyFirstReturn.p2m_local_no_early_three_torsion_return

