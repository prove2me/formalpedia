-- Prove2me | Theorems.Thm_lean_workbook_plus_61201
-- name    : lean_workbook_plus_61201
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/387f3139-d0d4-4ae6-84a3-cae50ad9ad0f
-- statement:
--   Prove that $ \frac{a^2+b^2}{a+b}+\frac{b^2+c^2}{b+c}+\frac{c^2+a^2}{c+a} \geq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61201 : ∀ a b c : ℝ, (a^2 + b^2) / (a + b) + (b^2 + c^2) / (b + c) + (c^2 + a^2) / (c + a) ≥ 3   :=  by sorry
