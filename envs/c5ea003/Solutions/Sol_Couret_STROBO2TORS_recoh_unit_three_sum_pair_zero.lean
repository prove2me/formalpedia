-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_unit_three_sum_pair_zero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:31.366807+00:00
-- url     : https://prove2.me/submissions/87cc737b-43fc-4dd4-afec-cf690ecf7b43

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

/-!
# Nonvanishing of three complex roots of 2-power order

The conjugation argument below supplies the symmetric-pair equation
that was an explicit hypothesis in `RecohThreeRootSymmetricGate`.
After normalization by the first root, the coprime-orders gate rules
out a vanishing sum of three roots whose orders divide powers of two.

The three roots need not be distinct. The exponents may differ.
This module proves nonvanishing; it does not assert that a character
bank is optimal or construct the bank required for reconstruction.
-/

namespace Couret.STROBO2TORS

/-- A normalized vanishing sum of three unit-modulus complex numbers
satisfies the symmetric-pair equation obtained by conjugation. -/
theorem p2m_local_recoh_unit_three_sum_pair_zero
    (b c : ℂ) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hsum : 1 + b + c = 0) :
    b + c + b * c = 0 := by
  have hbc : b * star b = 1 := by
    simpa [hb] using Complex.mul_conj' b
  have hcc : c * star c = 1 := by
    simpa [hc] using Complex.mul_conj' c
  have hconj : 1 + star b + star c = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg (starRingEnd ℂ) hsum
  calc
    b + c + b * c = (b * star b) * c + (c * star c) * b + b * c := by
      rw [hbc, hcc]
      ring
    _ = (1 + star b + star c) * (b * c) := by ring
    _ = 0 := by rw [hconj, zero_mul]









end Couret.STROBO2TORS


theorem solution : ∀ (b c : Complex),
  @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm b)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm c)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Eq.{1} Complex
          (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) b)
            c)
          (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) →
        @Eq.{1} Complex
          (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) b c)
            (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) b c))
          (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_unit_three_sum_pair_zero

