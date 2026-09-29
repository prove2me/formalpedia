-- Prove2me | Theorems.Thm_lean_workbook_plus_48982
-- name    : lean_workbook_plus_48982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/796dd0d1-a345-4c8f-bf3d-bfe363cd44cf
-- statement:
--   $ 1-(\frac{\sqrt{3}}{2})^2=1-\frac{3}{4}=\frac{1}{4}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48982 :
  1 - (Real.sqrt 3 / 2)^2 = 1 / 4   :=  by sorry
