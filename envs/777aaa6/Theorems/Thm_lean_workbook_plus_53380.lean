-- Prove2me | Theorems.Thm_lean_workbook_plus_53380
-- name    : lean_workbook_plus_53380
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/0d317ccb-53a8-4b51-a1be-3717adc756ec
-- statement:
--   Prove that $A^{3}+B^{3}+C^{3}-3ABC=(A+B+C)(A^{2}+B^{2}+C^{2}-AB-BC-CA)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53380 : ∀ a b c : ℤ, a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a)   :=  by sorry
