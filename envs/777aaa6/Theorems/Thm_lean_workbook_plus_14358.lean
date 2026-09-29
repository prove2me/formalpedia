-- Prove2me | Theorems.Thm_lean_workbook_plus_14358
-- name    : lean_workbook_plus_14358
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/6c2e472b-8965-4dcf-9665-161db1fb04d6
-- statement:
--   Let $x\geq -10.$ Prove that $(x^2+1)(x +7) +(x -10 )^2 \geq 97$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14358 : ∀ x : ℝ, x >= -10 → (x^2 + 1) * (x + 7) + (x - 10)^2 >= 97   :=  by sorry
