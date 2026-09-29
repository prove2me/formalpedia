-- Prove2me | Theorems.Thm_lindelof_hypothesis
-- name    : lindelof_hypothesis
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:48:27.795487+00:00
-- url     : https://prove2.me/theorems/9161859f-98c3-4232-89a0-c809a743100b
-- statement:
--   The Lindelöf hypothesis: The Riemann zeta function satisfies |ζ(1/2 + it)| = O(t^ε) for all ε > 0. Known: O(t^{13/84}) (Bourgain 2017). The best possible is O(t^ε) for all ε > 0. Equivalent to precise counting of zeros on the critical line; follows from RH but is strictly weaker.
-- source:
--   https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis

import Mathlib

import Mathlib

theorem lindelof_hypothesis :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta (1/2 + t * Complex.I)‖ ≤ C * t ^ eps := by
  sorry
