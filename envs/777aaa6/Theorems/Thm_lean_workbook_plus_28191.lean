-- Prove2me | Theorems.Thm_lean_workbook_plus_28191
-- name    : lean_workbook_plus_28191
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/61d342d2-ed2a-49c9-b5da-1c7097420916
-- statement:
--   Calculate: $\binom{6}{0}+\binom{6}{1}+\binom{6}{2}+\binom{6}{3}+\binom{6}{4}+\binom{6}{5}+\binom{6}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28191 : ∑ i in Finset.range 7, (Nat.choose 6 i) = 64   :=  by sorry
