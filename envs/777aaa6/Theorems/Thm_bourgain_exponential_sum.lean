-- Prove2me | Theorems.Thm_bourgain_exponential_sum
-- name    : bourgain_exponential_sum
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-06-01T01:39:58.856271+00:00
-- url     : https://prove2.me/theorems/a8d068a2-dd51-422b-aef0-6f6a7fd423ae
-- statement:
--   Bourgain's exponential sum theorem: For subsets A of ℤ/pℤ with |A| > p^{1/2+ε}, the exponential sum has nontrivial cancellation. Proved by Bourgain using sum-product methods. Optimal bounds for all sizes remain open.
-- source:
--   https://en.wikipedia.org/wiki/Bourgain%27s_theorem

import Mathlib

import Mathlib

theorem bourgain_exponential_sum (p : ℕ) (hp : Nat.Prime p) (delta : ℝ)
    (hdelta : 0 < delta ∧ delta < 1/2) :
    ∀ (A : Finset (ZMod p)),
      (p : ℝ) ^ (1/2 + delta) ≤ A.card →
      ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * a.val / p)‖ ≤
        (A.card : ℝ) * (p : ℝ) ^ (-delta / 2) := by
  sorry
