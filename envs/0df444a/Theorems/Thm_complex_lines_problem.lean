-- Prove2me | Theorems.Thm_complex_lines_problem
-- name    : complex_lines_problem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:51:35.318418+00:00
-- url     : https://prove2.me/theorems/22bd706e-ea70-46ee-96cf-e769710b420a
-- statement:
--   Sylvester-Gallai in ℂ (Kelly's theorem 1986): If every line through 2 points in ℂⁿ contains a 3rd, all points are collinear. Generalizations to higher fields and varieties remain open.
-- source:
--   https://en.wikipedia.org/wiki/Sylvester%E2%80%93Gallai_theorem

import Mathlib

import Mathlib

theorem complex_lines_problem (n : ℕ) (hn : 3 ≤ n)
    (pts : Fin n → ℂ)
    (hinj : Function.Injective pts)
    (hcoll : ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
      ∃ t : ℂ, pts a = pts b + t * (pts c - pts b)) :
    ∃ a b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      ∀ d : Fin n, ∃ t : ℂ, pts d = pts a + t * (pts b - pts a) := by
  sorry
