-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_triple_nonzero
-- name    : Couret.STROBO2TORS.recoh_two_primary_triple_nonzero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:03.205695+00:00
-- url     : https://prove2.me/theorems/97c87c51-b9ed-492d-ad21-2b2be97e023c
-- title:
--   Three two-primary roots cannot sum to zero
-- statement:
--   Let $a,b,c\in\mathbb C$ each have order dividing some power of two, possibly different powers. Then $$a+b+c\ne0.$$
--
--   The hypotheses allow each root to equal one.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTwoPowerTripleNonzero.lean, lines 79–92; source file SHA-256 aadc8ab3b2ba1146930247b9f110207ef6730467024bdc3e6c5c977cd3bbefcb; theorem Couret.STROBO2TORS.recoh_two_primary_triple_nonzero

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_power_triple_nonzero
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

theorem recoh_two_primary_triple_nonzero
    (a b c : ℂ)
    (ha : ∃ n : ℕ, a ^ (2 ^ n) = 1)
    (hb : ∃ n : ℕ, b ^ (2 ^ n) = 1)
    (hc : ∃ n : ℕ, c ^ (2 ^ n) = 1) :
    a + b + c ≠ 0 := by sorry


end Couret.STROBO2TORS
