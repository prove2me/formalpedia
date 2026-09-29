-- Prove2me | Theorems.Thm_lean_workbook_plus_21775
-- name    : lean_workbook_plus_21775
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/1b20387c-eee2-4c3b-913a-d4c5ab0f4651
-- statement:
--   Evaluate $1+2 \cdot 3+\cdots+98 \cdot 99+100$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21775 : ∑ i in Finset.range 101, i * (i + 1) = 4950   :=  by sorry
