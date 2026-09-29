-- Prove2me | Theorems.Thm_lean_workbook_plus_29336
-- name    : lean_workbook_plus_29336
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6991ed69-76fb-4825-a45f-c2b99e762924
-- statement:
--   Prove $2a^2+2b^2 \ge 2a^2b+2ab+(a-b)^2(a+b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29336 : ∀ a b : ℝ, 2 * a ^ 2 + 2 * b ^ 2 ≥ 2 * a ^ 2 * b + 2 * a * b + (a - b) ^ 2 * (a + b)   :=  by sorry
