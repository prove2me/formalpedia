-- Prove2me | Theorems.Thm_lean_workbook_plus_8114
-- name    : lean_workbook_plus_8114
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/820982dc-1682-4597-a4ae-b8bd2436688e
-- statement:
--   Prove that if $a^5-a^3+a=2$, then $a^3$ is greater than 3 and less than 4.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8114 (a : ℝ) (h : a^5 - a^3 + a = 2) : 3 < a^3 ∧ a^3 < 4   :=  by sorry
