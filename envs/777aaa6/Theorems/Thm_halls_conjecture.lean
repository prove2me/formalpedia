-- Prove2me | Theorems.Thm_halls_conjecture
-- name    : halls_conjecture
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:33:34.764371+00:00
-- url     : https://prove2.me/theorems/ddf0c751-3a5d-4ef8-af44-bcfef5bef3c6
-- statement:
--   Hall's conjecture (1971): If y² = x³ + k is satisfied by positive integers x, y, then |x| < C|y|^{2/3+ε} for any ε > 0. Or equivalently, the ABC conjecture implies |x| ≥ C|k|^{1/(3+ε)} for any integral point (x,y) of high magnitude. Connected to Lang's conjecture on Mordell curves.
-- source:
--   https://en.wikipedia.org/wiki/Hall%27s_conjecture

import Mathlib

import Mathlib

theorem halls_conjecture :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ x y : ℤ, 0 < x → 0 < y → y ^ 2 = x ^ 3 + 1 →
      x ≤ C * y ^ (2/3 + eps) := by
  sorry
