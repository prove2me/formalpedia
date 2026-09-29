-- Prove2me | Theorems.Thm_lean_workbook_plus_66023
-- name    : lean_workbook_plus_66023
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/38f965df-03f2-4162-9757-b27534b01b9e
-- statement:
--   This inequality is true using Cauchy : $9\left(a^{2} + 3b^{2} + 5c^{2}\right) = \left(1 + 3 + 5\right)\left(a^{2} + 3b^{2} + 5c^{2}\right)\ge\left(a + 3b + 5c\right)^{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66023 : ∀ a b c : ℝ, 9 * (a ^ 2 + 3 * b ^ 2 + 5 * c ^ 2) ≥ (a + 3 * b + 5 * c) ^ 2   :=  by sorry
