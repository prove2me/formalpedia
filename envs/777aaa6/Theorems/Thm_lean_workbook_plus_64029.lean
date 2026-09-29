-- Prove2me | Theorems.Thm_lean_workbook_plus_64029
-- name    : lean_workbook_plus_64029
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e7e936fc-c50c-491d-a8b2-2282bef43417
-- statement:
--   $ \sin{(C + C)} = \sin{C}\cos{C} + \cos{C}\sin{C} = 2\sin{C}\cos{C} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64029 :
  Real.sin (C + C) = 2 * Real.sin C * Real.cos C   :=  by sorry
