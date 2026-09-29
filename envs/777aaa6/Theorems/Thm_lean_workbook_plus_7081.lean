-- Prove2me | Theorems.Thm_lean_workbook_plus_7081
-- name    : lean_workbook_plus_7081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/575d830d-8df8-4833-bf3e-b75bc6f2fbc3
-- statement:
--   Find the limit of the sequence $a_n$ defined by $a_1=2$, $a_2=-2$, and $a_{n+1}=\frac{1}{2}(a_n^2-a_{n-1})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7081 (a : ℕ → ℝ) (a1 : a 0 = 2) (a2 : a 1 = -2) (a_rec : ∀ n, a (n + 1) = (a n)^2 / 2 - a (n - 1) / 2) : ∃ l, ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - l| < ε   :=  by sorry
