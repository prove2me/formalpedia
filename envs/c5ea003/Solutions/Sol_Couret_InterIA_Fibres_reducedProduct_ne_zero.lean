-- Prove2me | solution 1 for Couret.InterIA.Fibres.reducedProduct_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:59:49.438489+00:00
-- url     : https://prove2.me/submissions/44da776c-dde1-46e6-b047-59c0c62bb243

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial





/-- The coefficient obstruction is universal in m and in the nonzero real coefficients. -/
theorem p2m_local_reducedProduct_ne_zero (m r s : ℕ) (hr0 : 0 < r) (_hr : r < m)
    (hs0 : 0 < s) (_hs : s < m) (a b : ℝ) (ha : a ≠ 0) :
    reducedProduct m r s a b ≠ 0 := by
  intro hz
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hz
  by_cases hsmall : r+s < m
  · simp [reducedProduct,hsmall,coeff_monomial,hr0.ne',hs0.ne'] at h0
  · have hsum : r+s=m := by
      by_contra hn
      have hsum0 : r+s-m ≠ 0 := by omega
      simp [reducedProduct,hsmall,coeff_monomial,hr0.ne',hs0.ne',hsum0] at h0
    have hab : a*b=1 := by
      simp [reducedProduct,hsum,coeff_monomial,hr0.ne',hs0.ne'] at h0
      linarith
    have hR := congrArg (fun p : ℝ[X] => p.coeff r) hz
    dsimp only at hR
    unfold reducedProduct at hR
    rw [if_neg hsmall,hsum] at hR
    by_cases hrs : s=r
    · simp [coeff_one,coeff_C,hr0.ne',hrs] at hR
      have hb : b = -a := by linarith
      rw [hb] at hab
      nlinarith [sq_nonneg a]
    · simp [coeff_monomial,coeff_one,coeff_C,hr0.ne',hrs] at hR
      exact ha hR













end Couret.InterIA.Fibres

theorem solution : ∀ (m r s : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
    @LT.lt.{0} Nat instLTNat r m →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s →
        @LT.lt.{0} Nat instLTNat s m →
          ∀ (a b : Real),
            @Ne.{1} Real a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              @Ne.{1} (@Polynomial.{0} Real Real.semiring) (Couret.InterIA.Fibres.reducedProduct m r s a b)
                (@OfNat.ofNat.{0} (@Polynomial.{0} Real Real.semiring) (nat_lit 0)
                  (@Zero.toOfNat0.{0} (@Polynomial.{0} Real Real.semiring)
                    (@Polynomial.instZero.{0} Real Real.semiring))) := @_root_.Couret.InterIA.Fibres.p2m_local_reducedProduct_ne_zero

