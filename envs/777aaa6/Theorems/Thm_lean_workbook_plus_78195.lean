-- Prove2me | Theorems.Thm_lean_workbook_plus_78195
-- name    : lean_workbook_plus_78195
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/2bdc2323-9d30-491b-8c45-c04acbc0ab2e
-- statement:
--   Prove: $\frac{2 a (a - 1)^2 (2 a + 1)}{(a^2 + 2 a + 3) (3 a^2 + 2 a + 1)} \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78195 : ∀ a : ℝ, (2 * a * (a - 1) ^ 2 * (2 * a + 1)) / (a ^ 2 + 2 * a + 3) / (3 * a ^ 2 + 2 * a + 1) ≥ 0   :=  by sorry
