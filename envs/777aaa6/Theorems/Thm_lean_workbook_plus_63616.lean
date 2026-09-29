-- Prove2me | Theorems.Thm_lean_workbook_plus_63616
-- name    : lean_workbook_plus_63616
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/082e6917-9a5f-4cdd-965a-a0e547d61179
-- statement:
--   Summing this for n ranging from 1 to 50, we get: $ \sum_{j=1}^{50}100-2j = 2 \sum_{j=1}^{50}50-j = 2 \sum_{j=0}^{49}j = 49(49+1)=2450$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63616 :
  ∑ k in (Finset.range 50), (100 - (2 * (k + 1))) = 2450   :=  by sorry
