-- Prove2me | Theorems.Thm_lean_workbook_plus_67158
-- name    : lean_workbook_plus_67158
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/946c3638-2b50-4056-a47c-76d07ffbe1c8
-- statement:
--   Prove that the product of the first $1000$ positive even integers differs from the product of the first $1000$ positive odd integers by a multiple of $2001$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67158 : (∏ i in Finset.range 1000, (2 * i + 2)) - (∏ i in Finset.range 1000, (2 * i + 1)) ≡ 0 [ZMOD 2001]   :=  by sorry
