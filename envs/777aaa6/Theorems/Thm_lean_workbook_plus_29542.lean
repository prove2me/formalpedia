-- Prove2me | Theorems.Thm_lean_workbook_plus_29542
-- name    : lean_workbook_plus_29542
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d6638d84-9c3d-4088-b68f-c62db480a2d5
-- statement:
--   $ab^2(a+b)^3(a^2+b^2)=(b^4+2ab^3+a^2b^2)(a^4+a^3b+a^2b^2+ab^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29542 ∀ a b : ℝ, a * b^2 * (a + b)^3 * (a^2 + b^2) = (b^4 + 2 * a * b^3 + a^2 * b^2) * (a^4 + a^3 * b + a^2 * b^2 + a * b^3)   :=  by sorry
