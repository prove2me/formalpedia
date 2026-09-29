-- Prove2me | Theorems.Thm_mme_nat_pow_mul_factorial_le_self_pow_mul_factorial
-- name    : mme_nat_pow_mul_factorial_le_self_pow_mul_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:19:49.991848+00:00
-- url     : https://prove2.me/theorems/328b48b0-e5d7-4d98-87a2-51a4051a6f05
-- title:
--   An integral weight is a mode of its factorial-normalized powers
-- statement:
--   For natural numbers $w$ and $a$, the factorial-normalized power $w^a/a!$ is no larger than its value at $a=w$.  In division-free form,
--
--   $$
--   w^a w! \le w^w a!.
--   $$
--
--   Thus an integer $w$ is a mode of the sequence $w^a/a!$.  Applied in every cell of a multinomial table, the result gives a short exact comparison between a prescribed integral profile and competing profiles.  In the Coppersmith--Winograd outer laser argument, this is the elementary factorial kernel behind the dominant-profile bound.
-- source:
--   Elementary factorial inequality; used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), dominant-profile counting on pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Nat.Factorial.Basic

theorem mme_nat_pow_mul_factorial_le_self_pow_mul_factorial (w a : ℕ) :
    w ^ a * w.factorial ≤ w ^ w * a.factorial := by
  sorry
