-- Prove2me | Theorems.Thm_lean_workbook_plus_28716
-- name    : lean_workbook_plus_28716
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/18b0e6a5-4635-4f8e-9e75-624a804d4a9d
-- statement:
--   prove that: $6abc<ab(a+b)+bc(b+c)+ca(c+a)<2(a^{3}+b^{3}+c^{3})$ where a,b,c>0
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28716 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 6 * a * b * c < a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ∧ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) < 2 * (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
