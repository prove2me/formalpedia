-- Prove2me | Theorems.Thm_lean_workbook_plus_19344
-- name    : lean_workbook_plus_19344
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d06e4de1-97ed-4851-be2e-08974c1bbe04
-- statement:
--   $=\frac{(a+b+c)^{4}}{3abc(a+b+c)}\geq \frac{(a+b+c)^{4}}{(ab+bc+ca)^{2}}\geq \frac{3(a+b+c)^{2}}{ab+bc+ca}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19344 : ∀ a b c : ℝ, (a + b + c) ^ 4 / (3 * a * b * c * (a + b + c)) ≥ (a + b + c) ^ 4 / (a * b + b * c + c * a) ^ 2 ∧ (a + b + c) ^ 4 / (a * b + b * c + c * a) ^ 2 >= 3 * (a + b + c) ^ 2 / (a * b + b * c + c * a)   :=  by sorry
