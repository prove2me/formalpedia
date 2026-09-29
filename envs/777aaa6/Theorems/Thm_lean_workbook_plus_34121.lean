-- Prove2me | Theorems.Thm_lean_workbook_plus_34121
-- name    : lean_workbook_plus_34121
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/816c7f66-afec-477e-bdb1-e62b1cf02e21
-- statement:
--   Solve equation system\n $ x^3+y^2-2=0 \ x^2+y^2+xy-y=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34121 (x y : ℝ) (h₁ : x^3 + y^2 - 2 = 0) (h₂ : x^2 + y^2 + x*y - y = 0) : x = 1 ∧ y = 1   :=  by sorry
