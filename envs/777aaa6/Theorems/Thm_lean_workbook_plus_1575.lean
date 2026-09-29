-- Prove2me | Theorems.Thm_lean_workbook_plus_1575
-- name    : lean_workbook_plus_1575
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/95ff04fe-6c5d-4abb-928f-155214165d90
-- statement:
--   Show that $\frac12+\frac1{2^{2}}+...+\frac1{2^{n}}< 1$ , for all $n \in \mathbb{N}$ using only induction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1575 (n : ℕ) : ∑ i in Finset.range n, (1 / (2^(i + 1))) < 1   :=  by sorry
