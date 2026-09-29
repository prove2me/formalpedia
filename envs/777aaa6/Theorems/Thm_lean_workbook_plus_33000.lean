-- Prove2me | Theorems.Thm_lean_workbook_plus_33000
-- name    : lean_workbook_plus_33000
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/fdbe9380-a66a-4648-8b72-ec46b7593b43
-- statement:
--   Let $a \geq b \geq c >0$. Prove that: $\large\large \frac{a^{2}-b^{2}}{c}+\frac{c^{2}-b^{2}}{a}+\frac{a^{2}-b^{2}}{b}\geq 3a-4b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33000 : ∀ a b c : ℝ, a ≥ b ∧ b ≥ c ∧ c > 0 → (a^2 - b^2) / c + (c^2 - b^2) / a + (a^2 - b^2) / b ≥ 3 * a - 4 * b + c   :=  by sorry
