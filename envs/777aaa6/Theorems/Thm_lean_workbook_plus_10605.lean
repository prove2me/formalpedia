-- Prove2me | Theorems.Thm_lean_workbook_plus_10605
-- name    : lean_workbook_plus_10605
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/d7d0b459-46cd-46e5-96e8-87ab0dd4f652
-- statement:
--   prove that: $2(a^2+b^2+c^2)+3abc\geq9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10605 : ∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 3 * a * b * c ≥ 9   :=  by sorry
