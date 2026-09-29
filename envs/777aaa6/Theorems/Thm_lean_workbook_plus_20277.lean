-- Prove2me | Theorems.Thm_lean_workbook_plus_20277
-- name    : lean_workbook_plus_20277
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/7e2f0939-dddc-4ac2-a3e7-433f2ca4b6ce
-- statement:
--   f be a function satisfying $2f(x)+3f(-x)=x^2+5x$ . Find $f(7)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20277 (f : ℝ → ℝ) (h : ∀ x, 2 * f x + 3 * f (-x) = x^2 + 5 * x) : f 7 = -126 / 5   :=  by sorry
