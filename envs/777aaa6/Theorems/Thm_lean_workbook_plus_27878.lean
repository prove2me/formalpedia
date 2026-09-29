-- Prove2me | Theorems.Thm_lean_workbook_plus_27878
-- name    : lean_workbook_plus_27878
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/b737fbdf-a299-4f3d-972c-33495832bf73
-- statement:
--   Prove that if \( a,b,c\geq 0,\) then\n\n \( \frac{b+c}{a^2+bc}+\frac{c+a}{b^2+ca}+\frac{a+b}{c^2+ab}\geq\frac9{a+b+c}. \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27878 :  ∀ a b c : ℝ, a ≥ b ∧ b ≥ c ∧ c ≥ 0 → (b + c) / (a ^ 2 + b * c) + (c + a) / (b ^ 2 + c * a) + (a + b) / (c ^ 2 + a * b) ≥ 9 / (a + b + c)   :=  by sorry
