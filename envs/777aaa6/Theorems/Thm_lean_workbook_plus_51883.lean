-- Prove2me | Theorems.Thm_lean_workbook_plus_51883
-- name    : lean_workbook_plus_51883
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/8968a8ef-767b-4847-a187-f887843046bf
-- statement:
--   Prove that $-(x^2+y^2+z^2)(x-y-z)^2-2y^2z^2 \le 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51883 : ∀ x y z : ℝ, -(x^2+y^2+z^2)*(x-y-z)^2-2*y^2*z^2 ≤ 0   :=  by sorry
