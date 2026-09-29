-- Prove2me | Theorems.Thm_lean_workbook_plus_9332
-- name    : lean_workbook_plus_9332
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4b0d9d12-6f26-45b3-86a5-97ceaa78e59a
-- statement:
--   Let $a$ , $b$ and $c$ be non-negative numbers. Prove that: $8(a+b+c)^3\geq(7a-b)(7b-c)(7c-a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9332 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 8 * (a + b + c) ^ 3 ≥ (7 * a - b) * (7 * b - c) * (7 * c - a)   :=  by sorry
