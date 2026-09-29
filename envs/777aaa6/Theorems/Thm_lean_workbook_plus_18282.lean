-- Prove2me | Theorems.Thm_lean_workbook_plus_18282
-- name    : lean_workbook_plus_18282
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6fcc9fa7-0ab2-4ca1-98c0-4b6403f565a3
-- statement:
--   The real numbers $\alpha ,\beta$ satisfy the equations $$\alpha^3-3\alpha^2+5\alpha-17=0$$ $$\beta^3-3\beta^2+5\beta+11=0$$ Find $\alpha+\beta$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18282 (α β : ℝ) (h₁ : α^3 - 3 * α^2 + 5 * α - 17 = 0) (h₂ : β^3 - 3 * β^2 + 5 * β + 11 = 0) : α + β = 2   :=  by sorry
