-- Prove2me | Theorems.Thm_polynomial_freiman_ruzsa
-- name    : polynomial_freiman_ruzsa
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T21:05:23.475872+00:00
-- url     : https://prove2.me/theorems/c32c7ca4-070a-4b9c-90b2-405d84e0e8bd
-- statement:
--   Polynomial Freiman-Ruzsa conjecture (proved 2023): If |A+A| ≤ K|A|, then A is covered by a translate of a structured set of size poly(K)·|A|. Proved by Gowers–Green–Manners–Tao (2023). A major breakthrough in additive combinatorics.
-- source:
--   https://en.wikipedia.org/wiki/Freiman%E2%80%93Ruzsa_theorem

import Mathlib

import Mathlib

theorem polynomial_freiman_ruzsa (A : Finset ℤ)
    (K : ℝ) (hK : 1 ≤ K)
    (hA : ((A.image₂ (· + ·) A).card : ℝ) ≤ K * A.card) :
    ∃ (P H : Finset ℤ),
      (H.card : ℝ) ≤ K ^ 12 * A.card ∧
      A ⊆ H.image₂ (· + ·) P := by
  sorry
