-- Prove2me | Theorems.Thm_lean_workbook_plus_51370
-- name    : lean_workbook_plus_51370
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/26c2eb6c-238c-4a65-860b-3f09ed73ff9f
-- statement:
--   Prove that for any complex number $Z$, $|z-1/z|\le|z|+|1/z|$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51370 (z : ℂ) : ‖z - 1/z‖ ≤ ‖z‖ + ‖1/z‖   :=  by sorry
