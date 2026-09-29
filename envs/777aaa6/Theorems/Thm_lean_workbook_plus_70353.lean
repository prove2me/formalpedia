-- Prove2me | Theorems.Thm_lean_workbook_plus_70353
-- name    : lean_workbook_plus_70353
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/eb92136d-ec93-4f19-94d2-da8d9902573e
-- statement:
--   Prove that for $n=3$, if $0 < a \leq b \leq c$, then $\frac{a}{b} + \frac{b}{c} + \frac{c}{a} \geq \frac{b}{a} + \frac{c}{b} + \frac{a}{c}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70353 (a b c : ℝ) (h₁ : 0 < a ∧ 0 < b ∧ 0 < c) (h₂ : a ≤ b ∧ b ≤ c) : a / b + b / c + c / a ≥ b / a + c / b + a / c   :=  by sorry
