-- Prove2me | Theorems.Thm_lean_workbook_plus_62980
-- name    : lean_workbook_plus_62980
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/486c9b24-8fc4-4213-9d12-50b7e837bf3a
-- statement:
--   Given that $(a+1)(b+1)(c+1) = 8$ and $a, b, c\ge 0$, show that $abc\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62980 (a b c : ℝ) (h : (a + 1) * (b + 1) * (c + 1) = 8) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a * b * c ≤ 1   :=  by sorry
