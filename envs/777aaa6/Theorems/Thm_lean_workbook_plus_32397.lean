-- Prove2me | Theorems.Thm_lean_workbook_plus_32397
-- name    : lean_workbook_plus_32397
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d35b44d0-1cc9-4038-874f-4844e23fb046
-- statement:
--   Prove that for all positive real numbers $a, b$ : \n\n $ \frac {a+b} {a+b+1} < \frac {a} {a+1} + \frac {b} {b+1} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32397 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) / (a + b + 1) < a / (a + 1) + b / (b + 1)   :=  by sorry
