-- Prove2me | Theorems.Thm_lean_workbook_plus_2543
-- name    : lean_workbook_plus_2543
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/cca513fc-0f9c-4faf-880b-e2069241aba1
-- statement:
--   Prove that ${n\choose0}+{n\choose1}+{n\choose2}+{n\choose3}...{n\choose n}$ equals $2^{n}$ using Newton's binomial theorem.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2543 (n : ℕ) : ∑ k in Finset.range (n+1), choose n k = 2^n   :=  by sorry
