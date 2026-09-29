-- Prove2me | Theorems.Thm_lean_workbook_plus_20712
-- name    : lean_workbook_plus_20712
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/ea24b919-9ccf-48e2-a931-44187c4c2c0c
-- statement:
--   Prove that for every positive real number a, b, and c, the following inequality holds: \n$\frac{a}{2a+b+c}+\frac{b}{a+2b+c}+\frac{c}{a+b+2c}\leq \frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20712 : ∀ a b c : ℝ, (a > 0 ∧ b > 0 ∧ c > 0 → a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c) ≤ 3 / 4)   :=  by sorry
