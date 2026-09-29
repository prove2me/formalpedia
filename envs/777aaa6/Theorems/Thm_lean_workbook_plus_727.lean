-- Prove2me | Theorems.Thm_lean_workbook_plus_727
-- name    : lean_workbook_plus_727
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f21e6850-1704-49b6-a569-e6ae650a1611
-- statement:
--   Given $r = 1^{1/n}$, where $r$ is an nth root of unity, prove that $|r| = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_727 (n : ℕ) (hn : n ≠ 0) : ‖(1 : ℂ) ^ (1 / n : ℂ)‖ = 1   :=  by sorry
