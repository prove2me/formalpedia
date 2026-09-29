-- Prove2me | Theorems.Thm_lean_workbook_plus_61920
-- name    : lean_workbook_plus_61920
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/39dd3805-f0f8-4c8c-bb2f-41682dfadfae
-- statement:
--   Let $P(x,y)$ be the assertion $f(x+y)+f(x-y)-2f(x)f(1+y)=2xy(3y-x^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61920 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) + f (x - y) - 2 * f x * f (1 + y) = 2 * x * y * (3 * y - x ^ 2)) : ∃ c, ∀ x, f x = c * x ^ 3   :=  by sorry
