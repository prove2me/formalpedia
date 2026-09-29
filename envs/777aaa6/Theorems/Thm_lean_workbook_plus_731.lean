-- Prove2me | Theorems.Thm_lean_workbook_plus_731
-- name    : lean_workbook_plus_731
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8d94605c-0c0d-4f78-b1f8-9217b8e27845
-- statement:
--   $$\frac{a+b}{\sqrt{a^{2}+b}} + \frac{b+c}{\sqrt{b+c^{2}}} \leq \sqrt{2\left(\frac{(a+b)^2}{a^{2}+b} + \frac{(b+c)^2}{b+c^{2}} \right)}\leq2.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_731 : ∀ a b c : ℝ, (a + b) / Real.sqrt (a ^ 2 + b) + (b + c) / Real.sqrt (b + c ^ 2) ≤ Real.sqrt (2 * ((a + b) ^ 2 / (a ^ 2 + b) + (b + c) ^ 2 / (b + c ^ 2))) ∧ Real.sqrt (2 * ((a + b) ^ 2 / (a ^ 2 + b) + (b + c) ^ 2 / (b + c ^ 2))) ≤ 2   :=  by sorry
