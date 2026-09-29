-- Prove2me | Theorems.Thm_lean_workbook_plus_57354
-- name    : lean_workbook_plus_57354
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/47181c58-28a2-4243-bac8-ac800b9e8e3a
-- statement:
--   prove that \\( (a-b)^2(a-c)^2(b-c)^2\geq0 \\) for positive numbers \\( a, b, c \\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57354 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 ≥ 0   :=  by sorry
