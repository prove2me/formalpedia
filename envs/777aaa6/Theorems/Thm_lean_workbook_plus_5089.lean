-- Prove2me | Theorems.Thm_lean_workbook_plus_5089
-- name    : lean_workbook_plus_5089
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/34b3bc89-16c1-47fc-a172-7968892752b1
-- statement:
--   $ \\binom{n}{r}+\\binom{n}{r+1}= \\binom{n+1}{r+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5089 (n r : ℕ) : choose n r + choose n (r + 1) = choose (n + 1) (r + 1)   :=  by sorry
