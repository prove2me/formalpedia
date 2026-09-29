-- Prove2me | Theorems.Thm_lean_workbook_plus_16459
-- name    : lean_workbook_plus_16459
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e010d904-d800-4cba-94ce-e56c2ea8210d
-- statement:
--   Demonstrate the following equality: $ cos \frac{x}{2} cos \frac{x}{4} cos \frac{x}{8}.....cos \frac{x}{2^{2009}} = \frac {sin x} {2^{2009} sin (x/2^{2009})}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16459 : ∀ x : ℝ, (∏ i in Finset.range 2009, (cos (x / (2^i)))) = (sin x) / (2^2009 * sin (x / (2^2009)))   :=  by sorry
