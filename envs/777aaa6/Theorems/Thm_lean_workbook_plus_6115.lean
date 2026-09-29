-- Prove2me | Theorems.Thm_lean_workbook_plus_6115
-- name    : lean_workbook_plus_6115
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4ddc0d96-5a68-4e53-99c9-b81490b86841
-- statement:
--   Prove that the binomial coefficient $\binom{n}{r}$ is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6115 (n r : ℕ) : ∃ k, k = n.choose r   :=  by sorry
