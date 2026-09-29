-- Prove2me | Theorems.Thm_erdos_szemeredi_sum_product
-- name    : erdos_szemeredi_sum_product
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:25:17.282829+00:00
-- url     : https://prove2.me/theorems/3e8820a3-89b0-4a22-8701-c7714206fd2a
-- statement:
--   Erdős–Szemerédi sum-product conjecture (1983): For any finite set A of integers, max(|A+A|, |A·A|) ≥ C|A|^{2−ε} for any ε > 0. The best known bound is |A|^{4/3} (Solymosi 2009); the conjecture predicts the exponent approaches 2.
-- source:
--   https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Szemer%C3%A9di_theorem

import Mathlib

import Mathlib

theorem erdos_szemeredi_sum_product :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ (A : Finset ℤ), A.Nonempty →
      C * (A.card : ℝ) ^ (2 - eps) ≤
      max ((A ×ˢ A).image (fun p => p.1 + p.2)).card
          ((A ×ˢ A).image (fun p => p.1 * p.2)).card := by
  sorry
