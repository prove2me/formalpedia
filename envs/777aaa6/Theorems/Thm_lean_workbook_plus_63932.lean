-- Prove2me | Theorems.Thm_lean_workbook_plus_63932
-- name    : lean_workbook_plus_63932
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/7206c6e2-faef-4d9a-84f5-b1bb2322e14a
-- statement:
--   Prove that if $ a>1$ then $ \frac{1}{a-1}+\frac{1}{a}+\frac{1}{a+1}>\frac{3}{a}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63932 (a : ℝ) (ha : 1 < a) : 1 / (a - 1) + 1 / a + 1 / (a + 1) > 3 / a   :=  by sorry
