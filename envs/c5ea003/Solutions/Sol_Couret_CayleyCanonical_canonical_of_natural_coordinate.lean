-- Prove2me | solution 1 for Couret.CayleyCanonical.canonical_of_natural_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:47.314486+00:00
-- url     : https://prove2.me/submissions/70373b54-ccb7-48d6-81c0-31de159202d8

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyCanonical_canonical_of_bounded_coordinate
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



/-- Normalize an arbitrary coordinate modulo 3*ell using the group
element's additive order. The return conclusion is unchanged. -/
theorem p2m_local_canonical_of_natural_coordinate
    {Q : Type*} [AddCommGroup Q]
    (alpha delta : Q) (ell n : ℕ)
    (hell : 0 < ell)
    (hord : addOrderOf alpha = 3 * ell)
    (hcoordinate : n • alpha = delta)
    (hthree : (3 : ℕ) • delta = 0)
    (hne : delta ≠ 0) :
    ell • alpha = delta ∨ ell • alpha = -delta := by
  let k := n % (3 * ell)
  have hpositive : 0 < 3 * ell := by omega
  have hk : k < 3 * ell := Nat.mod_lt _ hpositive
  have hcoordinate' : k • alpha = delta := by
    dsimp [k]
    calc
      (n % (3 * ell)) • alpha =
          (n % addOrderOf alpha) • alpha := by rw [hord]
      _ = n • alpha := mod_addOrderOf_nsmul alpha n
      _ = delta := hcoordinate
  exact canonical_of_bounded_coordinate alpha delta ell k
    hell hord hk hcoordinate' hthree hne



end Couret.CayleyCanonical

namespace Couret.CayleyDoublet

open Couret.CayleyCanonical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]










end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {Q : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} Q] (alpha delta : Q) (ell n : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ell →
    @Eq.{1} Nat
        (@addOrderOf.{p2m_u_0} Q
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
            (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))
          alpha)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) ell) →
      @Eq.{p2m_u_0 + 1} Q
          (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
            (@instHSMul.{0, p2m_u_0} Nat Q
              (@AddMonoid.toNSMul.{p2m_u_0} Q
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
            n alpha)
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
                  delta)) := @_root_.Couret.CayleyCanonical.p2m_local_canonical_of_natural_coordinate

