-- Prove2me | Theorems.Thm_lean_workbook_plus_25992
-- name    : lean_workbook_plus_25992
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/dbc9acca-b774-4614-b8b7-3daef1329451
-- statement:
--   Let $a,b$ be positive real numbers such that $a+b=1$ . Prove that $ab^2\le\frac{4}{27}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25992 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a * b^2 ≤ 4/27   :=  by sorry
