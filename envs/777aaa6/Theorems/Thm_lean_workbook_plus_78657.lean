-- Prove2me | Theorems.Thm_lean_workbook_plus_78657
-- name    : lean_workbook_plus_78657
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b60b675a-31e4-4f5a-86f9-83827d4cb470
-- statement:
--   Prove that \(\frac{1}{2a} + \frac{1}{2b} + \frac{1}{2c} \ge \frac{1}{b + c} + \frac{1}{c + a} + \frac{1}{a + b}\) for \( a, b, c > 0 \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78657 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) ≥ 1 / (b + c) + 1 / (c + a) + 1 / (a + b)   :=  by sorry
