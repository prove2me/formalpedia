-- Prove2me | Theorems.Thm_lean_workbook_plus_42169
-- name    : lean_workbook_plus_42169
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/88e11d28-69d6-48df-bcb3-d9170febc2e2
-- statement:
--   If $a,b,c \in [1,2]$ then prove that : \n\n $$(a+5b+9c) \cdot \left ( \frac{1}{a} + \frac{5}{b} + \frac{9}{c} \right ) \le 225$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42169 : ∀ a b c : ℝ, a ∈ Set.Icc 1 2 ∧ b ∈ Set.Icc 1 2 ∧ c ∈ Set.Icc 1 2 → (a + 5 * b + 9 * c) * (1 / a + 5 / b + 9 / c) ≤ 225   :=  by sorry
