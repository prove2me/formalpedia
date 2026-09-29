-- Prove2me | Theorems.Thm_lean_workbook_plus_19710
-- name    : lean_workbook_plus_19710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/28d2ff5f-acc2-4060-a9fe-ab979c6f0326
-- statement:
--   all numbers $\le 40$ and of the form $4k+2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19710 : { n : ℕ | n ≤ 40 ∧ n % 4 = 2 } = { 2, 6, 10, 14, 18, 22, 26, 30, 34, 38 }   :=  by sorry
