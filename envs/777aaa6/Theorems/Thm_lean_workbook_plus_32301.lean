-- Prove2me | Theorems.Thm_lean_workbook_plus_32301
-- name    : lean_workbook_plus_32301
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b8806475-f426-4e90-8fdb-8740dd16fc45
-- statement:
--   Prove \n $\frac{1}{1 + 6x^2}\geq -\frac{24x}{25}+\frac{22}{25}$ for $x<\frac{1}{12}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32301 : ∀ x : ℝ, x < 1 / 12 → 1 / (1 + 6 * x ^ 2) ≥ -24 * x / 25 + 22 / 25   :=  by sorry
