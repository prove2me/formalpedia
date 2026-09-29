-- Prove2me | Theorems.Thm_lean_workbook_plus_59021
-- name    : lean_workbook_plus_59021
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9ad6c45e-84ab-469f-9ce1-01630953e53f
-- statement:
--   Compute $1\cdot1+2\cdot3+3\cdot5+\cdots+100\cdot199.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59021 : ∑ n in Finset.range 101, (n * (2 * n - 1)) = 665   :=  by sorry
