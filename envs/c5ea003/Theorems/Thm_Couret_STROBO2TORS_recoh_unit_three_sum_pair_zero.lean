-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_unit_three_sum_pair_zero
-- name    : Couret.STROBO2TORS.recoh_unit_three_sum_pair_zero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:29.893084+00:00
-- url     : https://prove2.me/theorems/2f74e950-c6f0-45b5-91d7-2cb71c478636
-- title:
--   A vanishing unit-circle triple gives the elementary symmetric identity
-- statement:
--   Let $b,c\in\mathbb C$ satisfy $|b|=|c|=1$ and $1+b+c=0$. Then
--
--   $$b+c+bc=0.$$
--
--   This algebraic consequence is used to analyze three-term root sums.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTwoPowerTripleNonzero.lean, lines 21–38; source file SHA-256 aadc8ab3b2ba1146930247b9f110207ef6730467024bdc3e6c5c977cd3bbefcb; theorem Couret.STROBO2TORS.recoh_unit_three_sum_pair_zero

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

theorem recoh_unit_three_sum_pair_zero
    (b c : ℂ) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hsum : 1 + b + c = 0) :
    b + c + b * c = 0 := by sorry










end Couret.STROBO2TORS
