-- Prove2me | Theorems.Thm_pell_equation_general
-- name    : pell_equation_general
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:43:26.026802+00:00
-- url     : https://prove2.me/theorems/48035570-3d49-4538-8bf4-3f9d86b7926b
-- statement:
--   Pell equation: x² - dy² = 1 has infinitely many integer solutions for non-square d. Proved (Lagrange). The fundamental solution and the continued fraction expansion give all solutions.
-- source:
--   https://en.wikipedia.org/wiki/Pell%27s_equation

import Mathlib

import Mathlib

theorem pell_equation_general (d : ℕ) (hd : ¬ ∃ k : ℕ, d = k ^ 2) :
    {(x, y) : ℤ × ℤ | x ^ 2 - d * y ^ 2 = 1}.Infinite := by
  sorry
