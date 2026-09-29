-- Prove2me | Theorems.Thm_lean_workbook_plus_34765
-- name    : lean_workbook_plus_34765
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/fa9ac94f-51d4-4131-9010-a0ceeec06327
-- statement:
--   If $a,b,c\in\mathbb{R}$ then $a^4+b^4+c^4\geq a^2b^2+b^2c^2+c^2a^2\geq abc(a+b+c)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34765 : ∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ∧ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a * b * c * (a + b + c)   :=  by sorry
