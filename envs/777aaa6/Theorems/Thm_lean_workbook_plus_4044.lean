-- Prove2me | Theorems.Thm_lean_workbook_plus_4044
-- name    : lean_workbook_plus_4044
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/edf94619-773b-4a55-9072-6ea7c2d6fda3
-- statement:
--   Find the value of $S = 2 + 4 + 6 + ... + 200$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4044 : ∑ k in Finset.range 101, 2 * k = 10100   :=  by sorry
