-- Prove2me | Theorems.Thm_mme_finset_factorial_mode_of_weighted_monomial_eq
-- name    : mme_finset_factorial_mode_of_weighted_monomial_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:27:47.334153+00:00
-- url     : https://prove2.me/theorems/74716afa-594c-4e5f-9c00-6d6892bcaf71
-- title:
--   Weighted-monomial equality implies factorial-profile dominance
-- statement:
--   Let $I$ be a finite index set and let $(w_i)$ be a positive integral profile.  If another integral profile $(a_i)$ has the same monomial in the weights,
--
--   $$
--   \prod_{i\in I} w_i^{a_i}=\prod_{i\in I} w_i^{w_i},
--   $$
--
--   then the factorial denominators satisfy
--
--   $$
--   \prod_{i\in I} w_i!\le\prod_{i\in I} a_i!.
--   $$
--
--   Equivalently, among profiles with the same weighted monomial and a common multinomial numerator, the coefficient of $w$ dominates the coefficient of $a$.  Exact product-form profiles in the Coppersmith--Winograd laser method satisfy the monomial hypothesis whenever the competing table has the same marginals.
-- source:
--   Elementary multinomial-mode comparison; used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), dominant-profile counting on pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib
import Theorems.Thm_mme_nat_pow_mul_factorial_le_self_pow_mul_factorial

open BigOperators

theorem mme_finset_factorial_mode_of_weighted_monomial_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (w a : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hpow : (∏ i, w i ^ a i) = ∏ i, w i ^ w i) :
    (∏ i, (w i).factorial) ≤ ∏ i, (a i).factorial := by
  sorry
