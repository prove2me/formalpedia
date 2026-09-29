-- Prove2me | Theorems.Thm_lean_workbook_plus_70087
-- name    : lean_workbook_plus_70087
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e68830ef-6a81-45f0-b0cc-19103d002f2e
-- statement:
--   Prove that $\frac{a^2+b^2+c^2}{ab+bc+ca}+\frac{8abc}{(a+b)(b+c)(c+a)}\ge 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70087 : ∀ a b c : ℝ, (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + (8 * a * b * c) / (a + b) / (b + c) / (c + a) ≥ 2   :=  by sorry
