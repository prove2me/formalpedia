-- Prove2me | Theorems.Thm_lean_workbook_plus_10968
-- name    : lean_workbook_plus_10968
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/f3a01e6a-4bd4-4d6d-981d-9353bde5611c
-- statement:
--   And we know (I am sure one can also prove it at ease) $\dbinom{n}{i} = \dbinom{n}{n-i} {\forall}i{\leq} n$ and $i {\in} {\mathbb{N}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10968 (n i : ℕ) (hi : i ≤ n) : choose n i = choose n (n-i)   :=  by sorry
