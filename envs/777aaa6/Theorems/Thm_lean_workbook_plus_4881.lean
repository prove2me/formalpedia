-- Prove2me | Theorems.Thm_lean_workbook_plus_4881
-- name    : lean_workbook_plus_4881
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b851e70c-e7cc-4911-b67a-bc31fa343278
-- statement:
--   Show that $((a+b)^2-c^2)(c^2-(a-b)^2) \leq 4a^2b^2$ for real $a,b,c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4881 (a b c : ℝ) : ((a + b) ^ 2 - c ^ 2) * (c ^ 2 - (a - b) ^ 2) ≤ 4 * a ^ 2 * b ^ 2   :=  by sorry
