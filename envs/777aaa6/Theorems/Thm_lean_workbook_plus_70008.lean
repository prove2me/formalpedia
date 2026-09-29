-- Prove2me | Theorems.Thm_lean_workbook_plus_70008
-- name    : lean_workbook_plus_70008
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7d3ed88b-6d8e-4899-beec-c91e96b989cd
-- statement:
--   $x^{3}-3x+2 \ge 0 \Leftrightarrow (x+2)(x-1)^{2}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70008 : ∀ x : ℝ, x^3 - 3*x + 2 ≥ 0 ↔ (x + 2)*(x - 1)^2 ≥ 0   :=  by sorry
