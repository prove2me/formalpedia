-- Prove2me | Theorems.Thm_lean_workbook_plus_23198
-- name    : lean_workbook_plus_23198
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/6f87e912-b20a-4d49-aacd-26e093dd6e46
-- statement:
--   Prove $ \frac{a^{2}+b^{2}c}{b+c} +\frac{b^{2}+c^{2}a}{a+c}+\frac{c^{2}+a^{2}b}{a+b}\geq \frac{2}{3} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23198 : ∀ a b c : ℝ, (a^2 + b^2 * c) / (b + c) + (b^2 + c^2 * a) / (a + c) + (c^2 + a^2 * b) / (a + b) ≥ 2 / 3   :=  by sorry
