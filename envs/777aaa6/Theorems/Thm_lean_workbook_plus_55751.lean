-- Prove2me | Theorems.Thm_lean_workbook_plus_55751
-- name    : lean_workbook_plus_55751
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/be7654f9-8c82-43b8-91a7-5dc3326e49cb
-- statement:
--   Squaring both sides, we have: $ab(a+b) + bc(b+c) + ca(c+a) + 2\sqrt{a^2bc(a+b)(a+c)} + 2\sqrt{ab^2c(b+a)(b+c)} + 2\sqrt{abc^2(c+a)(c+b)}\geq 4abc + (a+b)(b+c)(c+a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55751 : ∀ a b c : ℝ, a * b * (a + b) + b * c * (b + c) + c * a * (c + a) + 2 * Real.sqrt (a ^ 2 * b * c * (a + b) * (a + c)) + 2 * Real.sqrt (a * b ^ 2 * c * (b + a) * (b + c)) + 2 * Real.sqrt (a * b * c ^ 2 * (c + a) * (c + b)) ≥ 4 * a * b * c + (a + b) * (b + c) * (c + a)   :=  by sorry
