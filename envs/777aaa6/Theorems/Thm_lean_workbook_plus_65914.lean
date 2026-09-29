-- Prove2me | Theorems.Thm_lean_workbook_plus_65914
-- name    : lean_workbook_plus_65914
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4c1dbab9-d86b-4186-800d-b177535624a0
-- statement:
--   Ratio test: Show that $\frac{(a+1)^{(a+2)}}{a^{a+1}} \geq \frac{(a+2)^{(a+1)}}{(a+1)^a}$ implies $(a+1)^2 \geq a(a+2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65914 (a : ℝ) (ha : a > 0) : (a + 1) ^ (a + 2) / a ^ (a + 1) ≥ (a + 2) ^ (a + 1) / (a + 1) ^ a → (a + 1) ^ 2 ≥ a * (a + 2)   :=  by sorry
