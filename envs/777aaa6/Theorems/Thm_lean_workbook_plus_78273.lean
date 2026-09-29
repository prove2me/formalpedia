-- Prove2me | Theorems.Thm_lean_workbook_plus_78273
-- name    : lean_workbook_plus_78273
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e3df2ee4-a0f6-40bd-ab1c-1183cda12e59
-- statement:
--   Again, by Cauchy, $ (1 + 1 + 1)(a^2 + b^2 + c^2)\geq(a + b + c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78273  (a b c : ℝ) :
  (1 + 1 + 1) * (a^2 + b^2 + c^2) ≥ (a + b + c)^2   :=  by sorry
