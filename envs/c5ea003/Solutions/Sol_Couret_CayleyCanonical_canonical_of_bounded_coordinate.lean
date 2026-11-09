-- Prove2me | solution 1 for Couret.CayleyCanonical.canonical_of_bounded_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:41:29.372909+00:00
-- url     : https://prove2.me/submissions/d80a9c38-2c2e-4134-9047-293c0399263d

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 -- canonical order-three return in the odd cyclic quotient.
Research source, **UNCOMPILED** with pinned Lean 4.29.1.
No existing certified theorem has been modified.

The first lemma needs only the order of alpha and a bounded coordinate,
and is independent of any representation of a directed graph. The last
lemma translates its canonical witness back to the quotient G/<h>.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyCanonical

/-- For alpha of order 3*ell, a nonzero three-torsion element represented
by a bounded natural multiple k<3*ell must equal either ell*alpha or its additive inverse. -/
theorem p2m_local_canonical_of_bounded_coordinate
    {Q : Type*} [AddCommGroup Q]
    (alpha delta : Q) (ell k : ℕ)
    (hell : 0 < ell)
    (hord : addOrderOf alpha = 3 * ell)
    (hk : k < 3 * ell)
    (hcoordinate : k • alpha = delta)
    (hthree : (3 : ℕ) • delta = 0)
    (hne : delta ≠ 0) :
    ell • alpha = delta ∨ ell • alpha = -delta := by
  have hzero : (3 * k) • alpha = 0 := by
    rw [mul_nsmul', hcoordinate, hthree]
  have hdiv : 3 * ell ∣ 3 * k := by
    rw [← hord]
    exact (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hzero
  have hdivell : ell ∣ k := by
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hdiv
  obtain ⟨m, hm⟩ := hdivell
  have hmlt : m < 3 := by
    have hmul : ell * m < ell * 3 := by
      simpa [hm, Nat.mul_comm] using hk
    exact (Nat.mul_lt_mul_left hell).mp hmul
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hd0 : delta = 0 := by
      have h := hcoordinate
      simp [hm, h0] at h
      exact h.symm
    exact (hne hd0).elim
  · left
    simpa [hm, h1] using hcoordinate
  · right
    have hbeta : (3 : ℕ) • (ell • alpha) = 0 := by
      rw [← mul_nsmul', ← hord]
      exact addOrderOf_nsmul_eq_zero alpha
    have hdouble : (2 : ℕ) • (ell • alpha) = -(ell • alpha) := by
      have hh : (2 : ℕ) • (ell • alpha) + (ell • alpha) = 0 := by
        simpa [three_nsmul, two_nsmul, add_assoc] using hbeta
      exact eq_neg_of_add_eq_zero_left hh
    have hd : delta = -(ell • alpha) := by
      have h := hcoordinate
      rw [hm, h2, mul_nsmul] at h
      exact h.symm.trans hdouble
    simp [hd]





end Couret.CayleyCanonical

namespace Couret.CayleyDoublet

open Couret.CayleyCanonical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]










end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {Q : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} Q] (alpha delta : Q) (ell k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ell →
    @Eq.{1} Nat
        (@addOrderOf.{p2m_u_0} Q
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
            (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))
          alpha)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell) →
      @LT.lt.{0} Nat instLTNat k
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell) →
        @Eq.{p2m_u_0 + 1} Q
            (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
              (@instHSMul.{0, p2m_u_0} Nat Q
                (@AddMonoid.toNSMul.{p2m_u_0} Q
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
              k alpha)
            delta →
          @Eq.{p2m_u_0 + 1} Q
              (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
                (@instHSMul.{0, p2m_u_0} Nat Q
                  (@AddMonoid.toNSMul.{p2m_u_0} Q
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) delta)
              (@OfNat.ofNat.{p2m_u_0} Q (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} Q
                  (@NegZeroClass.toZero.{p2m_u_0} Q
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} Q
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} Q
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} Q
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} Q inst))))))) →
            @Ne.{p2m_u_0 + 1} Q delta
                (@OfNat.ofNat.{p2m_u_0} Q (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} Q
                    (@NegZeroClass.toZero.{p2m_u_0} Q
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} Q
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} Q
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} Q
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} Q inst))))))) →
              Or
                (@Eq.{p2m_u_0 + 1} Q
                  (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
                    (@instHSMul.{0, p2m_u_0} Nat Q
                      (@AddMonoid.toNSMul.{p2m_u_0} Q
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
                    ell alpha)
                  delta)
                (@Eq.{p2m_u_0 + 1} Q
                  (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
                    (@instHSMul.{0, p2m_u_0} Nat Q
                      (@AddMonoid.toNSMul.{p2m_u_0} Q
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
                    ell alpha)
                  (@Neg.neg.{p2m_u_0} Q
                    (@NegZeroClass.toNeg.{p2m_u_0} Q
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} Q
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} Q
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} Q
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} Q inst)))))
                    delta)) := @_root_.Couret.CayleyCanonical.p2m_local_canonical_of_bounded_coordinate

