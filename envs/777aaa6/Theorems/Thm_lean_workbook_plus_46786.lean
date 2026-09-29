-- Prove2me | Theorems.Thm_lean_workbook_plus_46786
-- name    : lean_workbook_plus_46786
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ba7ab2d1-ca45-46cc-babb-16d8bb652ea5
-- statement:
--   Strengthening: Given $a, b, c \geq 0$ and $ab + bc + ca = 1$, prove that $\frac{a^{2}}{b} + \frac{b^{2}}{c} + \frac{c^{2}}{a} - 2(a^{2} + b^{2} + c^{2}) \geq a + b + c - 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46786 :  ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a * b + b * c + c * a = 1 → a ^ 2 / b + b ^ 2 / c + c ^ 2 / a - 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a + b + c - 2   :=  by sorry
