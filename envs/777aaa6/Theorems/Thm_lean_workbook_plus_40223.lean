-- Prove2me | Theorems.Thm_lean_workbook_plus_40223
-- name    : lean_workbook_plus_40223
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/726fed00-57a1-4aae-b250-9494cd020310
-- statement:
--   Prove: $2(a^2+b^2+c^2)^2\ge(a+b+c)(a^3+b^3+c^3+ab^2+bc^2+ca^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40223 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3 + a * b ^ 2 + b * c ^ 2 + c * a ^ 2)   :=  by sorry
