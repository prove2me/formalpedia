-- Prove2me | Theorems.Thm_lean_workbook_plus_80302
-- name    : lean_workbook_plus_80302
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/804c5742-5cf4-4a92-b211-498e4f55fe6f
-- statement:
--   Prove that $x^3+y^3+(-xy)^3-3xy(-xy)=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80302 : ∀ x y : ℤ, x^3 + y^3 + (-x * y)^3 - 3 * x * y * (-x * y) = 0   :=  by sorry
