-- Prove2me | Theorems.Thm_lean_workbook_plus_49281
-- name    : lean_workbook_plus_49281
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/80abf9c9-901f-4cfc-b2ee-57040c769fd5
-- statement:
--   Given $\alpha, \beta$ are real numbers satisfying ${\alpha}^3-3{\alpha}^2+5{\alpha}=1$ and ${\beta}^3-3{\beta}^2+5{\beta}=5$ . Find $\alpha +\beta$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49281 (α β : ℝ) (h₁ : α^3 - 3 * α^2 + 5 * α = 1) (h₂ : β^3 - 3 * β^2 + 5 * β = 5) : α + β = 2   :=  by sorry
