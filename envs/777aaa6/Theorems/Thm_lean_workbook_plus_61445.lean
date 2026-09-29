-- Prove2me | Theorems.Thm_lean_workbook_plus_61445
-- name    : lean_workbook_plus_61445
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/1a71b25d-3a5c-49cf-9572-bbd81228fd5b
-- statement:
--   Prove $2 + 4 + 6 + \dots + 2n = n^2 + n,$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61445 : ∀ n, ∑ i in Finset.range n, 2 * i = n^2 + n   :=  by sorry
