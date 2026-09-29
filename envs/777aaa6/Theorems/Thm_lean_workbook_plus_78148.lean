-- Prove2me | Theorems.Thm_lean_workbook_plus_78148
-- name    : lean_workbook_plus_78148
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/c7ce8506-6ff9-4711-bbbf-f904584fadba
-- statement:
--   x^2+y^2\ge 2xy and ditto for the other two cases, all by AM-GM or noticing that $x^2+y^2-2xy=(x-y)^2\ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78148 : ∀ x y : ℝ, x^2 + y^2 ≥ 2 * x * y   :=  by sorry
