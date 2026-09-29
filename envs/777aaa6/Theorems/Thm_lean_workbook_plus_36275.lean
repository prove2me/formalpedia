-- Prove2me | Theorems.Thm_lean_workbook_plus_36275
-- name    : lean_workbook_plus_36275
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/684afbb0-1ebd-4115-b1a5-bf789adc6dbc
-- statement:
--   Calculate $a_1$ for the sequence $a_n=\sqrt{n(n+1)}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36275 (a : ℕ → ℝ) (a_def : ∀ n, a n = Real.sqrt (n * (n + 1))) : a 1 = Real.sqrt 2   :=  by sorry
