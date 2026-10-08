-- Prove2me | Theorems.Thm_Goldbach_weighted_convolution_extract_prime_pair
-- name    : Goldbach.weighted_convolution_extract_prime_pair
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T01:21:58.440763+00:00
-- url     : https://prove2.me/theorems/0aceb3d6-1bde-4de1-a0b4-08732ec1a39e
-- title:
--   Extract a prime pair from the sharper weighted convolution threshold
-- statement:
--   Let
--
--   $$R(N)=\sum_{m=0}^{N}\Lambda(m)\Lambda(N-m).$$
--
--   If
--
--   $$R(N)>2\lfloor\sqrt N\rfloor(\log N)^2,$$
--
--   then `N` is the sum of two primes. This improves the earlier extraction
--   criterion by removing its extra `floor(log₂ N)` factor.
--
--   The proof uses the refined weighted proper-prime-power bound. If no prime pair
--   exists, every term of the full convolution is a bad-pair term, so the full sum
--   is at most the stated contamination bound. This contradicts the strict
--   hypothesis. The finite sum includes both endpoints, and the argument applies to
--   every natural `N` without an omitted small-number case.
--
--   The submitted source includes the complete weighted-contamination proof and
--   imports no open platform theorem. This establishes a sufficient condition; it
--   does not establish that condition for every large even number. Strong Goldbach
--   and its uniform binary-correlation input remain unresolved.
-- source:
--   Elementary weighted prime-power bounds and an improved quantitative extraction interface for https://prove2.me/missions/The_Goldbach_Conjecture. Uses Mathlib vonMangoldt_apply_pow and the integer-log power bound; no new prime-distribution estimate or literature novelty is claimed.

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.weighted_convolution_extract_prime_pair (N : ℕ)
    (hlarge : 2 * (Nat.sqrt N : ℝ) * (Real.log N)^2 <
      ∑ m ∈ Finset.range (N+1),
        ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N-m)) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ N = p+q := by sorry
