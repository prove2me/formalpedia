-- Prove2me | Theorems.Thm_lean_workbook_plus_61203
-- name    : lean_workbook_plus_61203
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/14feede5-54a0-46b6-979e-030042eb04d0
-- statement:
--   Prove that $4^n\geq{(n+1)^3} $ for any $n\geq3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61203 (n : ℕ) (h : n ≥ 3) : 4 ^ n ≥ (n + 1) ^ 3   :=  by sorry
