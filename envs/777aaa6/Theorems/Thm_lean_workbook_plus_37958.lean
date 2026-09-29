-- Prove2me | Theorems.Thm_lean_workbook_plus_37958
-- name    : lean_workbook_plus_37958
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d5ce68e2-d113-487f-bb13-c31f7d8dc316
-- statement:
--   Prove that, $2(a^5+b^5+c^5)\ge ab^4+bc^4+ca^4+a^4b+b^4c+c^4a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37958 : ∀ a b c : ℝ, 2 * (a ^ 5 + b ^ 5 + c ^ 5) ≥ a * b ^ 4 + b * c ^ 4 + c * a ^ 4 + a ^ 4 * b + b ^ 4 * c + c ^ 4 * a   :=  by sorry
