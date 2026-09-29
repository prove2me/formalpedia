-- Prove2me | Theorems.Thm_lean_workbook_plus_38292
-- name    : lean_workbook_plus_38292
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/54e4ee98-3dd8-4e4b-a27b-30f59ebb1fea
-- statement:
--   Prove that $(1-2t)(t-\frac{1}{3})^{2} \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38292 : ∀ t : ℝ, (1 - 2 * t) * (t - 1 / 3) ^ 2 ≥ 0   :=  by sorry
