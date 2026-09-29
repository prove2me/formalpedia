-- Prove2me | Theorems.Thm_lean_workbook_plus_10625
-- name    : lean_workbook_plus_10625
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2d943cc2-75ba-4a0d-bf98-afb338b13dc3
-- statement:
--   Prove that for real numbers, $|a| \leq b$ implies $-b \leq a \leq b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10625 (a b : ℝ) (h : |a| ≤ b) : -b ≤ a ∧ a ≤ b   :=  by sorry
