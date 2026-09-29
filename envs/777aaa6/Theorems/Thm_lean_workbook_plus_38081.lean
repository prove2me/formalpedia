-- Prove2me | Theorems.Thm_lean_workbook_plus_38081
-- name    : lean_workbook_plus_38081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/c2137df1-8394-4965-91ab-05b052971595
-- statement:
--   Trivial by seesaw formula. \n\n \(96x=72(14-x)\) Solving, we get $\boxed{x=6.}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38081  (x : ℝ)
  (h₀ : 96 * x = 72 * (14 - x)) :
  x = 6   :=  by sorry
