-- Prove2me | Theorems.Thm_lean_workbook_plus_78617
-- name    : lean_workbook_plus_78617
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/c61fa2ff-a4a2-4acd-a006-4d8599318dfb
-- statement:
--   Find the value of $f(3)$ if $f(x) = 2x + 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78617 (f : ℝ → ℝ) (h₁ : ∀ x, f x = 2 * x + 1) : f 3 = 7   :=  by sorry
