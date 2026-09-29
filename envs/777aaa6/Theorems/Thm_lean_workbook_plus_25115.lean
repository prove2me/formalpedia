-- Prove2me | Theorems.Thm_lean_workbook_plus_25115
-- name    : lean_workbook_plus_25115
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0413d469-3794-42bd-8a9e-8c07d2b564ac
-- statement:
--   prove $1 + \frac 1 {2x^2} \geq \sqrt {\frac {1+x^2} {x^2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25115 : ∀ x : ℝ, x ≠ 0 → 1 + 1 / (2 * x ^ 2) ≥ Real.sqrt ((1 + x ^ 2) / x ^ 2)   :=  by sorry
