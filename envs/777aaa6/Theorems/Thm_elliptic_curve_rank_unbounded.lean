-- Prove2me | Theorems.Thm_elliptic_curve_rank_unbounded
-- name    : elliptic_curve_rank_unbounded
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:04:39.459249+00:00
-- url     : https://prove2.me/theorems/33240bc0-1757-4cf0-b391-bedd6af0f2d0
-- statement:
--   Elliptic curve rank unboundedness: Are there elliptic curves over ℚ with arbitrarily large rank? Current record: rank ≥ 29 (Elkies–Klagsbrun 2024). No proof of unboundedness; BSD conjecture predicts rank = order of vanishing of L-function at s=1.
-- source:
--   https://en.wikipedia.org/wiki/Elliptic_curve

import Mathlib

import Mathlib

theorem elliptic_curve_rank_unbounded :
    ∀ n : ℕ, ∃ (a b : ℤ) (_ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0),
      n ≤ {pt : ℚ × ℚ | (pt.2)^2 = (pt.1)^3 + (a : ℚ) * pt.1 + b}.ncard := by
  sorry
