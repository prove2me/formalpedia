-- Prove2me | Theorems.Thm_lean_workbook_plus_78605
-- name    : lean_workbook_plus_78605
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/70578068-d435-4e8d-8531-92c5bf56113c
-- statement:
--   prove that: \n$\frac{a^{2}}{2b+c}+\frac{b^{2}}{2c+a}+\frac{ c^{2}}{2a+b}\geq \frac{a^{2}+b^{2}+c^{2}}{a+b+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78605 : ∀ a b c : ℝ, (a^2 / (2 * b + c) + b^2 / (2 * c + a) + c^2 / (2 * a + b) : ℝ) ≥ (a^2 + b^2 + c^2) / (a + b + c)   :=  by sorry
