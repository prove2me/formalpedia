-- Prove2me | Theorems.Thm_lean_workbook_plus_5395
-- name    : lean_workbook_plus_5395
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/dff40d51-9bcc-40b8-8f45-7ddb5560d7d1
-- statement:
--   while $ x \in (0,1)$ we have $ \frac {(1 - x)^3}{1 + 2x}\geq \frac {116}{225} - \frac {76x}{75}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5395  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x < 1) :
  (1 - x) ^ 3 / (1 + 2 * x) ≥ 116 / 225 - 76 * x / 75   :=  by sorry
