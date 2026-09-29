-- Prove2me | Theorems.Thm_lean_workbook_plus_78100
-- name    : lean_workbook_plus_78100
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/31291a13-e34e-442a-ad68-5aa59965cc44
-- statement:
--   Prove the inequality $(b+c-a)^{2}+(c+a-b)^{2} \geq 2(a-b)^{2}$ for non-negative numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78100 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (b + c - a) ^ 2 + (c + a - b) ^ 2 ≥ 2 * (a - b) ^ 2   :=  by sorry
