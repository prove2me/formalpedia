-- Prove2me | Theorems.Thm_lean_workbook_plus_72704
-- name    : lean_workbook_plus_72704
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4d2f21b3-8702-4f16-9c48-ffebd93f167f
-- statement:
--   Show that the equation $x^4+x^3-x+1=0$ doesn't have any real solution.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72704 : ¬ ∃ x : ℝ, x^4 + x^3 - x + 1 = 0   :=  by sorry
