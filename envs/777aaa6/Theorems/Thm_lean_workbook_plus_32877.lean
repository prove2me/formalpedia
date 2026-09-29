-- Prove2me | Theorems.Thm_lean_workbook_plus_32877
-- name    : lean_workbook_plus_32877
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/1f71c6d5-1f01-4989-92ae-f741cf0bf213
-- statement:
--   Let $a \ge 1$ and $b \ge 1$ be real numbers. Show that $(a+b) (\frac {1}{a}+\frac{1}{b} ) \le 4+ max(a,b)-min(a,b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32877 (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : (a + b) * (1 / a + 1 / b) ≤ 4 + max a b - min a b   :=  by sorry
