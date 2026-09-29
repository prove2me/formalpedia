-- Prove2me | Theorems.Thm_lean_workbook_plus_68772
-- name    : lean_workbook_plus_68772
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5baddac7-2b5b-4706-8b00-899dfecddb9a
-- statement:
--   Prove that $\binom{2n}{n} = \binom{n}{0}^2 + \binom{n}{1}^2 + \ldots + \binom{n}{n-1}^2 + \binom{n}{n}^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68772 : ∀ n : ℕ, (Nat.choose 2 * n) n = ∑ i in Finset.range n.succ, (Nat.choose n i)^2   :=  by sorry
