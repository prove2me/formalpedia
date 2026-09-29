-- Prove2me | Theorems.Thm_lean_workbook_plus_70233
-- name    : lean_workbook_plus_70233
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e1c2476d-c139-4a18-8034-eba322b06aae
-- statement:
--   $0=x_1x_2x_3^2+x_1x_3+x_2x_3+x_3^2=(x_1x_3+1)(x_2x_3+1)+x_3^2-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70233 : ∀ x1 x2 x3 : ℂ, 0 = x1 * x2 * x3 ^ 2 + x1 * x3 + x2 * x3 + x3 ^ 2 ↔ 0 = (x1 * x3 + 1) * (x2 * x3 + 1) + x3 ^ 2 - 1   :=  by sorry
