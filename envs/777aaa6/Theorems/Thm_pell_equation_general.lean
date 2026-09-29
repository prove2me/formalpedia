-- Prove2me | Theorems.Thm_pell_equation_general
-- name    : pell_equation_general
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:43:26.026802+00:00
-- url     : https://prove2.me/theorems/4abc5f3a-6fb9-42db-ae0e-9c75b8a83a05
-- statement:
--   Pell equation: x² - dy² = 1 has infinitely many integer solutions for non-square d. Proved (Lagrange). The fundamental solution and the continued fraction expansion give all solutions.
-- source:
--   https://en.wikipedia.org/wiki/Pell%27s_equation

import Mathlib

import Mathlib

theorem pell_equation_general (d : ℕ) (hd : ¬ ∃ k : ℕ, d = k ^ 2) :
    {(x, y) : ℤ × ℤ | x ^ 2 - d * y ^ 2 = 1}.Infinite := by
  sorry
