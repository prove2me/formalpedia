-- Prove2me | Theorems.Thm_lean_workbook_plus_77497
-- name    : lean_workbook_plus_77497
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/23498dbb-768a-47ac-99ac-85f5f683de02
-- statement:
--   prove $ \frac{b^2+c^2}{b+c}+\frac{c^2+a^2}{c+a}+\frac{a^2+b^2}{a+b}\geq a+b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77497 : ∀ a b c : ℝ, (b^2 + c^2) / (b + c) + (c^2 + a^2) / (c + a) + (a^2 + b^2) / (a + b) ≥ a + b + c   :=  by sorry
