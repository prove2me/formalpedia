-- Prove2me | Theorems.Thm_lean_workbook_plus_14395
-- name    : lean_workbook_plus_14395
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8a745caf-9798-4df5-8f17-c94200aa3d2e
-- statement:
--   Easy to see that $3 \le x \le 9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14395 (x : ℝ) (hx : x ∈ Set.Icc 3 9) : 3 ≤ x ∧ x ≤ 9   :=  by sorry
