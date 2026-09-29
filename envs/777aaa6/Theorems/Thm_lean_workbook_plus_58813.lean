-- Prove2me | Theorems.Thm_lean_workbook_plus_58813
-- name    : lean_workbook_plus_58813
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a713e32c-2934-4988-9f5c-fe86d263099e
-- statement:
--   If $ a,b,c$ are real numbers, then \n\n $ \left(a^2+b^2+c^2+5bc+5ca+5ab\right)^2\geq 12(a+b+c)^2(bc+ca+ab), $\n\n with equality if and only if $ a=b=c.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58813 (a b c : ℝ) : (a^2 + b^2 + c^2 + 5 * b * c + 5 * c * a + 5 * a * b)^2 ≥ 12 * (a + b + c)^2 * (b * c + c * a + a * b)   :=  by sorry
