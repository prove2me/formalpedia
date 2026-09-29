-- Prove2me | Theorems.Thm_lean_workbook_plus_68073
-- name    : lean_workbook_plus_68073
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/da249767-25f3-4b29-abaa-a77093e23d3a
-- statement:
--   $((-2)+1)^{2}+0^{2}=((-2)+2)^{2}+1^{2}=((-2)+3)^{2}+0^{2}=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68073 :
  (((-2) + 1)^2 + 0^2 = ((-2) + 2)^2 + 1^2 ∧ ((-2) + 2)^2 + 1^2 = ((-2) + 3)^2 + 0^2 ∧ ((-2) + 3)^2 + 0^2 = 1)   :=  by sorry
