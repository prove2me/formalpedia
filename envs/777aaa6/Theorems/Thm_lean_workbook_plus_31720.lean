-- Prove2me | Theorems.Thm_lean_workbook_plus_31720
-- name    : lean_workbook_plus_31720
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/05645b41-a1be-420e-8c6d-2231bfd389ec
-- statement:
--   What is the mean of $0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31720 : ∑ i in Finset.range 16, (if i < 15 then 0 else 16) / 16 = 1   :=  by sorry
