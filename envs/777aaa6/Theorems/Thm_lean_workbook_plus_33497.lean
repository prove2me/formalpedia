-- Prove2me | Theorems.Thm_lean_workbook_plus_33497
-- name    : lean_workbook_plus_33497
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/136483e1-666d-4578-99f4-25c9d2351ef3
-- statement:
--   Prove that \n\n $ \frac{a^2+b^2}{a+b}+\frac{c^2+a^2}{c+a}+\frac{b^2+c^2}{b+c}\geq a+b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33497 : ∀ a b c : ℝ, (a^2 + b^2) / (a + b) + (c^2 + a^2) / (c + a) + (b^2 + c^2) / (b + c) ≥ a + b + c   :=  by sorry
