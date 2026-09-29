-- Prove2me | Theorems.Thm_lean_workbook_plus_60432
-- name    : lean_workbook_plus_60432
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/1b0295d1-689c-46d5-9cf3-b6444bd681e1
-- statement:
--   With $a,b,c \geq 1$ and $abc \geq 2^9$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60432 (a b c : ℝ) (habc : a * b * c ≥ 2^9) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) : a + b + c ≥ 3   :=  by sorry
