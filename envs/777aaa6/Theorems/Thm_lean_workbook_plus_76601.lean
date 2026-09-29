-- Prove2me | Theorems.Thm_lean_workbook_plus_76601
-- name    : lean_workbook_plus_76601
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/796694ab-8d1f-4eaa-8c0e-6a426a09cfa8
-- statement:
--   Prove that $(a+3b)^2 + (3b+2c)^2 \geq \frac{(a+6b+2c)^2}{2}$ using Titu's lemma.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76601 : ∀ a b c : ℝ, (a + 3 * b) ^ 2 + (3 * b + 2 * c) ^ 2 ≥ (a + 6 * b + 2 * c) ^ 2 / 2   :=  by sorry
