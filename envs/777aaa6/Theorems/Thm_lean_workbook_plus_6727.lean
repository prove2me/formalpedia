-- Prove2me | Theorems.Thm_lean_workbook_plus_6727
-- name    : lean_workbook_plus_6727
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/fc83e10f-881e-40c1-b322-a8674c696f9e
-- statement:
--   Characteristic polynomial of a $2 \times 2$ matrix: $x^2 - (\text{trace }A)x + \det A$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6727 (x : ℂ) (a b c d : ℂ) :
  (a - x) * (d - x) - b * c = x^2 - (a + d) * x + (a * d - b * c)   :=  by sorry
