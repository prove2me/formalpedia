-- Prove2me | Theorems.Thm_lean_workbook_plus_60540
-- name    : lean_workbook_plus_60540
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/dd7ad9ed-6e11-4546-9cea-df8c2ebfcc7b
-- statement:
--   Prove that $\binom{n}{0} - \binom{n}{1} + \binom{n}{2} - \cdots + (-1)^n \binom{n}{n} = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60540 : ∀ n : ℕ, ∑ k in Finset.range (n + 1), (-1 : ℤ)^k * (n.choose k) = 0   :=  by sorry
