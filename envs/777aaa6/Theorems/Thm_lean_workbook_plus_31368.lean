-- Prove2me | Theorems.Thm_lean_workbook_plus_31368
-- name    : lean_workbook_plus_31368
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/2601e082-b3c4-4d28-8238-0b287c5d0b63
-- statement:
--   So we want to prove that $\dbinom{n+1}{2}=1+2+\cdots+n.$ Clearly, $\dbinom{n+1}{2}$ counts the number of unordered pairs of integers $(i,j)$ with $i\neq j$ such that $1\leq i,j\leq n+1.$ We will count this in a different way.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31368 (n : ℕ) : (n + 1).choose 2 = (∑ i in Finset.range (n + 1), i)   :=  by sorry
