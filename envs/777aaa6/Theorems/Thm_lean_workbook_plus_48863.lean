-- Prove2me | Theorems.Thm_lean_workbook_plus_48863
-- name    : lean_workbook_plus_48863
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/a0e2a7bd-e162-4201-8f70-7f6cfa513ace
-- statement:
--   Prove that the sequence $(-1)^n$ diverges.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48863 : ¬ ∃ l, ∀ n, |(-1 : ℝ)^n - l| < 1   :=  by sorry
