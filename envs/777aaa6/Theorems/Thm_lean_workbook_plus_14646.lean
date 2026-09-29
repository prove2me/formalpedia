-- Prove2me | Theorems.Thm_lean_workbook_plus_14646
-- name    : lean_workbook_plus_14646
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/69dafe16-d3fb-4438-ba89-ed9a9d56495a
-- statement:
--   Prove that for all $x > 0$, $\sqrt{x + 2\sqrt{x - 1}} + \sqrt{x - 2\sqrt{x - 1}} = 2\sqrt{x - 1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14646 : ∀ x > 0, Real.sqrt (x + 2 * Real.sqrt (x - 1)) + Real.sqrt (x - 2 * Real.sqrt (x - 1)) = 2 * Real.sqrt (x - 1)   :=  by sorry
