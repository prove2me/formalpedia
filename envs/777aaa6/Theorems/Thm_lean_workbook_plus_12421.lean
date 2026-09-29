-- Prove2me | Theorems.Thm_lean_workbook_plus_12421
-- name    : lean_workbook_plus_12421
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/fb81d63d-d918-4c87-a5c7-85c69e6ce1a9
-- statement:
--   Prove that for $0\le x\le 1$, $0 \le x-x^2 \le \frac{1}{4}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12421 (x : ℝ) (hx: 0 ≤ x ∧ x ≤ 1) : 0 ≤ x - x^2 ∧ x - x^2 ≤ 1/4   :=  by sorry
