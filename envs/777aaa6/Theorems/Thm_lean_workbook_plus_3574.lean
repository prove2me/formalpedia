-- Prove2me | Theorems.Thm_lean_workbook_plus_3574
-- name    : lean_workbook_plus_3574
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d4757926-b9ab-4dcd-b7e6-e345b0a8655a
-- statement:
--   Prove that $1+2+3+4+...+n=\binom{1}{1}+\binom{2}{1}+\dots +\binom{n}{1}=\binom{n+1}{2}$ using Hockey Stick Identity
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3574 (n : ℕ) : ∑ i in Finset.range (n+1), i = (n + 1).choose 2   :=  by sorry
