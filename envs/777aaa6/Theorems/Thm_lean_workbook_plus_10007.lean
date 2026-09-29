-- Prove2me | Theorems.Thm_lean_workbook_plus_10007
-- name    : lean_workbook_plus_10007
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a34d3e5c-3939-484e-8f03-afad88f2ef6c
-- statement:
--   Prove that \n $\binom{n}{0}+\binom{n}{1}+.......+\binom{n}{n-1}+\binom{n}{n}=2^{n}$\nJust use the Newton binomila formula for the $(1+1)^n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10007 : ∀ n : ℕ, ∑ k in Finset.range (n+1), (Nat.choose n k) = 2^n   :=  by sorry
