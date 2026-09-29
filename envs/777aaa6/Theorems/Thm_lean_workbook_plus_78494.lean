-- Prove2me | Theorems.Thm_lean_workbook_plus_78494
-- name    : lean_workbook_plus_78494
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e8cec92e-1159-478a-a6ef-65f75a840480
-- statement:
--   Find a sequence ${ v_{n} }$ such that ${ v_{n} } = 1$ if $n$ is odd and ${ v_{n} } = 1/n$ if $n$ is even.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78494 : ∃ (v : ℕ → ℝ), ∀ n, Odd n → v n = 1 ∧ Even n → v n = 1 / n   :=  by sorry
