-- Prove2me | Theorems.Thm_lean_workbook_plus_49546
-- name    : lean_workbook_plus_49546
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/a38ba2b3-0ed7-488f-b4ef-d97d19d490b9
-- statement:
--   On Sola's first birthday, he got $10$ dollars. Every subsequent year's birthday, he got $3$ more dollars than the previous year. On his twelfth birthday, how much money in dollars had he gotten from all the birthdays?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49546 : ∑ k in Finset.range 12, (10 + 3 * k) = 318   :=  by sorry
