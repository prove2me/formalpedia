-- Prove2me | Theorems.Thm_lean_workbook_plus_9739
-- name    : lean_workbook_plus_9739
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/08990c81-69a7-4584-a145-20b214d9f4d7
-- statement:
--   If $z_1=c-a-x$ and $z_2=d-b-y$, show that $(2c-2a-z_1)^2+(2d-2b-z_2)^2=z_1^2+z_2^2=(2a+z_1)^2+(2b+z_2)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9739 : ∀ c a x d b y z₁ z₂ : ℝ,  z₁ = c - a - x ∧ z₂ = d - b - y → (2 * c - 2 * a - z₁) ^ 2 + (2 * d - 2 * b - z₂) ^ 2 = z₁ ^ 2 + z₂ ^ 2 ∧ z₁ ^ 2 + z₂ ^ 2 = (2 * a + z₁) ^ 2 + (2 * b + z₂) ^ 2   :=  by sorry
