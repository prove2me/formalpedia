-- Prove2me | Theorems.Thm_lean_workbook_plus_58181
-- name    : lean_workbook_plus_58181
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/72d0c704-64a9-4cf0-926f-f4d30135173a
-- statement:
--   Charlie has a chocolate factory that produces $1$ chocolate on its opening day, $3$ on its second day, $6$ on its third day, and so on. On the $n$ th day, the factory produces $n$ more chocolates than the day before. How many chocolates in total will have been produced at the end of the $12$ th day?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58181 : ∑ k in Finset.range 12, (k + 1) = 364   :=  by sorry
