-- Prove2me | Theorems.Thm_lean_workbook_plus_79174
-- name    : lean_workbook_plus_79174
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/2c83b245-fe2e-46fd-9563-c64c69007912
-- statement:
--   Since $Z\ge{2Y^2-Y}$ and $0\le{Y}\le{1}$, prove: $\frac{2Y^2-Y}{3}+1\ge{\frac{4\sqrt{3}}{9}Y\sqrt{1+2Y}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79174 : ∀ y : ℝ, y ∈ Set.Icc 0 1 → (2 * y ^ 2 - y) / 3 + 1 ≥ (4 * Real.sqrt 3) / 9 * y * (Real.sqrt (1 + 2 * y))   :=  by sorry
