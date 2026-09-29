-- Prove2me | Theorems.Thm_lean_workbook_plus_29239
-- name    : lean_workbook_plus_29239
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/cd0bf543-4c56-49a0-927c-5ef2021b6f24
-- statement:
--   Take $n=2m^2$ and see that $4m^4+1 = (2m^2+1)^2-(2m)^2= (2m^2-2m+1)(2m^2+2m+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29239  (m : ℤ) :
  4 * m^4 + 1 = (2 * m^2 + 1)^2 - (2 * m)^2   :=  by sorry
