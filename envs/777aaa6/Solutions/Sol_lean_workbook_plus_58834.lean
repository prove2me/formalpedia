-- Prove2me | solution 1 for lean_workbook_plus_58834
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:51.960767+00:00
-- url     : https://prove2.me/submissions/2da58269-c224-4988-8cac-4df4539d7762

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1000000

theorem solution (a b c : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (h : ∀ n, x (n + 3) = a * x (n + 2) - b * x (n + 1) + c * x n) :
    (x (n + 6))^2 = (a^2 - b) * (x (n + 5))^2 +
      (a * c + b^2 - a^2 * b) * (x (n + 4))^2 +
      (a^3 * c + b^3 + 2 * c^2 - 4 * a * b * c) * (x (n + 3))^2 +
      (a^2 * c^2 + b * c^2 - a * b^2 * c) * (x (n + 2))^2 +
      (b^2 * c^2 - a * c^3) * (x (n + 1))^2 - c^4 * (x n)^2 := by
  have h3 := h n
  have h4 : x (n + 4) = a * x (n + 3) - b * x (n + 2) + c * x (n + 1) := by
    simpa [Nat.add_assoc] using h (n + 1)
  have h5 : x (n + 5) = a * x (n + 4) - b * x (n + 3) + c * x (n + 2) := by
    simpa [Nat.add_assoc] using h (n + 2)
  have h6 : x (n + 6) = a * x (n + 5) - b * x (n + 4) + c * x (n + 3) := by
    simpa [Nat.add_assoc] using h (n + 3)
  rw [h6, h5, h4, h3]
  ring
