-- Prove2me | Theorems.Thm_lean_workbook_plus_26684
-- name    : lean_workbook_plus_26684
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ed2d0696-34ff-462f-9935-9f0b884baca2
-- statement:
--   The given sum is equivalent to $\binom{2}{2}+\binom{3}{2}+\binom{4}{2}+\dots+\binom{2009}{2}+\binom{2010}{2}+\binom{2011}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26684 (n : ℕ) : ∑ k in Finset.Icc 2 2011, (Nat.choose k 2) = 1355454220   :=  by sorry
