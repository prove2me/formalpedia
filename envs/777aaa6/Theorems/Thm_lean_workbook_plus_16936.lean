-- Prove2me | Theorems.Thm_lean_workbook_plus_16936
-- name    : lean_workbook_plus_16936
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/76f6acf2-869d-46cf-b0e3-142726f61c4e
-- statement:
--   Prove the following Identity: $\binom{n}{0}+\binom{n+1}{1}+\binom{n+2}{2}+\binom{n+3}{3}+....+\binom{n+r}{r} = \binom{n+r+1}{r}$ Assume that $n$ be a fixed positive integer, then use mathematical induction on $r$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16936 (n r : ℕ) : ∑ i in Finset.range (r+1), (n+i).choose i = (n+r+1).choose r   :=  by sorry
