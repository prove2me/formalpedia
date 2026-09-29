-- Prove2me | Theorems.Thm_lean_workbook_plus_15896
-- name    : lean_workbook_plus_15896
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d327924a-2db2-4de9-a0e1-2cc22ff9605c
-- statement:
--   Prove that for any three positive real numbers $ a,b,c, \frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a} \ge \frac{9}{2} \cdot \frac{1}{a+b+c}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15896 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥ 9 / 2 * (1 / (a + b + c))   :=  by sorry
