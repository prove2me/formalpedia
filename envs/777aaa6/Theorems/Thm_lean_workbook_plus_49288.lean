-- Prove2me | Theorems.Thm_lean_workbook_plus_49288
-- name    : lean_workbook_plus_49288
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/4db2263a-5609-4be3-913c-9b8141541ed7
-- statement:
--   Clarify the properties of absolute value: $|x| = x$ if $x$ is non-negative and $|x| = -x$ if $x$ is negative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49288 (x : ℝ) : (x ≥ 0 → |x| = x) ∧ (x < 0 → |x| = -x)   :=  by sorry
