-- Prove2me | Theorems.Thm_lean_workbook_plus_49123
-- name    : lean_workbook_plus_49123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/4a63df0d-160d-426d-8217-87c3e720ce10
-- statement:
--   Prove that: $1/(a-b)^2+1/(b-c)^2+1/(c-a)^2=(1/(a-b)+1/(b-c)+1/(c-a))^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49123 {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : 1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2 = (1 / (a - b) + 1 / (b - c) + 1 / (c - a)) ^ 2   :=  by sorry
