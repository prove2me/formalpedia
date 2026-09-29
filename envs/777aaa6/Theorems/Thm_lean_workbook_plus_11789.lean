-- Prove2me | Theorems.Thm_lean_workbook_plus_11789
-- name    : lean_workbook_plus_11789
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4959a990-6272-4e5d-8df5-bba66e2f4258
-- statement:
--   Let $ f $ be a function with real number as its domain that satisfies the conditions $ f(x+y)=f(x)f(y) $ , for all $ x $ and $ y $ and $ f(0) \neq 0 $ . Prove that $ f(x) \neq 0 $ for all real value of $ x $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11789 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f x * f y) (h : f 0 ≠ 0) : ∀ x, f x ≠ 0   :=  by sorry
