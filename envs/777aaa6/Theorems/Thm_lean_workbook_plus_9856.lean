-- Prove2me | Theorems.Thm_lean_workbook_plus_9856
-- name    : lean_workbook_plus_9856
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/922ff2c5-58ce-42e4-96c4-e9777d224701
-- statement:
--   Is this the correct statement? $\\left(\\frac{{23+\sqrt{513}}}{4}\\right)\\left({\\frac{{23-\sqrt{513}}}{4}}\\right)=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9856 :
  (1 / 4 * (23 + Real.sqrt 513)) * (1 / 4 * (23 - Real.sqrt 513)) = 1   :=  by sorry
