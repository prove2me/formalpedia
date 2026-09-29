-- Prove2me | Theorems.Thm_lean_workbook_plus_32084
-- name    : lean_workbook_plus_32084
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0418768b-7433-4d3e-a4f7-967f3f82af83
-- statement:
--   Prove the convergence of the infinite geometric series for $|z| < 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32084 (z : ℂ) (hz : Complex.abs z < 1) : ∃ y, ∑' n : ℕ, z ^ n = y   :=  by sorry
