-- Prove2me | Theorems.Thm_perfect_difference_set
-- name    : perfect_difference_set
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:25:45.376346+00:00
-- url     : https://prove2.me/theorems/0ec1764c-5fde-4dda-96bd-084845af4e36
-- statement:
--   Perfect difference set / cyclic difference set: A (q²+q+1, q+1, 1)-difference set D in ℤ/(q²+q+1)ℤ exists for every prime power q. Equivalent to projective planes. Existence for non-prime-power q (if any projective planes of non-prime-power order exist) is open.
-- source:
--   https://en.wikipedia.org/wiki/Difference_set

import Mathlib

import Mathlib

theorem perfect_difference_set (q : ℕ) (hq : 2 ≤ q) (hpow : ∃ p k : ℕ, Nat.Prime p ∧ q = p ^ k) :
    ∃ (D : Finset (ZMod (q^2 + q + 1))),
      D.card = q + 1 ∧
      ∀ d : ZMod (q^2 + q + 1), d ≠ 0 →
        ∃! p : D × D, p.1 ≠ p.2 ∧ p.1.val - p.2.val = d := by
  sorry
