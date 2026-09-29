-- Prove2me | Theorems.Thm_lean_workbook_plus_58504
-- name    : lean_workbook_plus_58504
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2127b38b-6b8f-4014-9acb-29e38259ee17
-- statement:
--   If $a$ , $b$ , $c$ are real numbers, prove that $\frac{a+b}{2b+c}+\frac{b+c}{2c+a}+\frac{c+a}{2a+b} \geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58504 : ∀ a b c : ℝ, (a + b) / (2 * b + c) + (b + c) / (2 * c + a) + (c + a) / (2 * a + b) ≥ 2   :=  by sorry
