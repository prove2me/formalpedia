-- Prove2me | Theorems.Thm_lean_workbook_plus_11003
-- name    : lean_workbook_plus_11003
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/91b05174-6437-4482-be49-7d43b8f15cba
-- statement:
--   Prove that there exists infinitely many positive integers n such that $4n^{2}+1$ is divisible both by 5 and 13.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11003 : ∃ n : ℕ, 5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1   :=  by sorry
