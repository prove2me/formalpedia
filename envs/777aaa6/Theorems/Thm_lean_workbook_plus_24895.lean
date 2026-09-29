-- Prove2me | Theorems.Thm_lean_workbook_plus_24895
-- name    : lean_workbook_plus_24895
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1bc565bb-ba67-4fe4-ae6a-c0675e1e7cdd
-- statement:
--   Use Legendre's formula to prove that $\binom{n}{r}$ is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24895 (n r : ℕ) : ∃ k : ℕ, (k : ℚ) = choose n r   :=  by sorry
