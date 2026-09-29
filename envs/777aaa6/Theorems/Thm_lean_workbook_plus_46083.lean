-- Prove2me | Theorems.Thm_lean_workbook_plus_46083
-- name    : lean_workbook_plus_46083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4cf41f34-176d-4926-8ae7-16400fbc77be
-- statement:
--   Let $a,b,c>0$ Prove that: $ \frac{a-b}{b+c }+ \frac{b-c}{c+a }+ \frac{c-a}{a+b } \geq 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46083 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a - b) / (b + c) + (b - c) / (c + a) + (c - a) / (a + b) ≥ 0   :=  by sorry
