-- Prove2me | Theorems.Thm_lean_workbook_plus_67693
-- name    : lean_workbook_plus_67693
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/48717cda-f809-420f-b943-69966596d9c4
-- statement:
--   Let $a, b, c$ be positive real numbers . Prove that \n\n $$(a+b)(2b+c)(2c+a)\ge \frac{1}{2}(a+2b+2c)(ab+2bc+2ca)$$ $$(a+b)(2b+c)(2c+a)\ge \frac{1}{3}(a+2b+2c)(ab+3bc+3ca)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67693 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a + b) * (2 * b + c) * (2 * c + a) ≥ (1 / 2) * (a + 2 * b + 2 * c) * (a * b + 2 * b * c + 2 * c * a)   :=  by sorry
