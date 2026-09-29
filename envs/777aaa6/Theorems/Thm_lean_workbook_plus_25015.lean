-- Prove2me | Theorems.Thm_lean_workbook_plus_25015
-- name    : lean_workbook_plus_25015
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/9fef4fa7-8a7c-45af-8dfb-275d76186057
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $\frac{a^2}{a+b}+\frac{b^2}{b+c}+\frac{c^2}{c+a}\ge \frac{a+b+c}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25015 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^2 / (a + b) + b^2 / (b + c) + c^2 / (c + a) ≥ (a + b + c) / 2   :=  by sorry
