-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_two_power_triple_nonzero
-- name    : Couret.STROBO2TORS.recoh_two_power_triple_nonzero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:47:22.505134+00:00
-- url     : https://prove2.me/theorems/c48534e1-b462-4458-b1ae-d6f82a2c3332
-- title:
--   Three roots of common two-power order cannot sum to zero
-- statement:
--   For natural $n$ and complex $a,b,c$ satisfying $a^{2^n}=b^{2^n}=c^{2^n}=1$, $$a+b+c\ne0.$$
--
--   This includes $n=0$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTwoPowerTripleNonzero.lean, lines 59–77; source file SHA-256 aadc8ab3b2ba1146930247b9f110207ef6730467024bdc3e6c5c977cd3bbefcb; theorem Couret.STROBO2TORS.recoh_two_power_triple_nonzero

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_Couret_STROBO2TORS_recoh_symmetric_three_sum_two_power_impossible
import Theorems.Thm_Couret_STROBO2TORS_recoh_unit_three_sum_pair_zero
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

theorem recoh_two_power_triple_nonzero
    (n : ℕ) (a b c : ℂ)
    (ha : a ^ (2 ^ n) = 1) (hb : b ^ (2 ^ n) = 1)
    (hc : c ^ (2 ^ n) = 1) :
    a + b + c ≠ 0 := by sorry




end Couret.STROBO2TORS
