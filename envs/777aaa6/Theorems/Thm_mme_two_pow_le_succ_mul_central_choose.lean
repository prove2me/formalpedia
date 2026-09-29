-- Prove2me | Theorems.Thm_mme_two_pow_le_succ_mul_central_choose
-- name    : mme_two_pow_le_succ_mul_central_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:04:50.156769+00:00
-- url     : https://prove2.me/theorems/43ac5032-598c-4912-a288-e1d0c507811c
-- title:
--   Polynomial lower bound for the central binomial coefficient
-- statement:
--   For every natural number $n$, the central binomial coefficient contains at least a $1/(n+1)$ fraction of the full binomial mass:
--
--   $$2^n\le(n+1)\binom{n}{\lfloor n/2\rfloor}.$$
--
--   This elementary polynomial lower bound controls the loss incurred by requiring a prescribed balanced half of a word.
-- source:
--   Binomial theorem and maximality of the central binomial coefficient; applied to the common-halving refinement of Duan--Wu--Zhou, arXiv:2210.10173v5, Section 6.3.

import Mathlib.Data.Nat.Choose.Sum

open BigOperators Finset

set_option autoImplicit false

theorem mme_two_pow_le_succ_mul_central_choose (n : ℕ) :
    2 ^ n ≤ (n + 1) * Nat.choose n (n / 2) := by
  sorry
