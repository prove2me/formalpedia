-- Prove2me | Theorems.Thm_lean_workbook_plus_81978
-- name    : lean_workbook_plus_81978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/a340e7ff-faa7-4a96-a886-6c6c9a9826c3
-- statement:
--   Prove that for $a, b, c, d > 0$, \n $ \frac{(a-b)^2}{a+b}+\frac{(c-d)^2}{c+d}\ge\frac{(a+c-b-d)^2}{a+b+c+d} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81978 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a - b) ^ 2 / (a + b) + (c - d) ^ 2 / (c + d) ≥ (a + c - b - d) ^ 2 / (a + b + c + d)   :=  by sorry
