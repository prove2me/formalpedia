-- Prove2me | Theorems.Thm_lean_workbook_plus_30300
-- name    : lean_workbook_plus_30300
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c854f585-4d4f-464e-92ef-2f19c3179a1a
-- statement:
--   For $a,b,c>0$ Prove that: $\sum_{cyc}\frac{a^2}{a^2+ab+b^2}\ge \frac{a+b+c}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30300 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a^2/(a^2 + a * b + b^2) + b^2/(b^2 + b * c + c^2) + c^2/(c^2 + c * a + a^2) : ℝ) ≥ (a + b + c) / 3   :=  by sorry
