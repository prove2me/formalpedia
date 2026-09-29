-- Prove2me | Theorems.Thm_lean_workbook_plus_5177
-- name    : lean_workbook_plus_5177
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/95108238-3a3a-46f2-8766-be1df1c2c43f
-- statement:
--   Show that for positive real numbers a, b, and c, the following inequality holds:\n\(a^3+b^3+c^3+24abc\le(a+b+c)^3\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5177 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 24 * a * b * c ≤ (a + b + c)^3   :=  by sorry
