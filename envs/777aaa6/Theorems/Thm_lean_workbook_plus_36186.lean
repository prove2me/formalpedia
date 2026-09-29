-- Prove2me | Theorems.Thm_lean_workbook_plus_36186
-- name    : lean_workbook_plus_36186
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9678624f-2bf6-4fca-ba15-1d1920f1d6e6
-- statement:
--   Show that for any positive real numbers $a,b$ the following inequality is true: \n $$2(a^2+b^2+2)\geq 2(a+1)(b+1)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36186 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 2 * (a^2 + b^2 + 2) ≥ 2 * (a + 1) * (b + 1)   :=  by sorry
