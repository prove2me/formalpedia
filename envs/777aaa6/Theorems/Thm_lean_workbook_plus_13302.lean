-- Prove2me | Theorems.Thm_lean_workbook_plus_13302
-- name    : lean_workbook_plus_13302
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4355c66a-7265-42b7-a5a7-ef0a630a3b63
-- statement:
--   Function $sin (x) $ have zeros $x=0, k \pi,-{k \pi } $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13302 (x : ℝ) : sin x = 0 ↔ ∃ k : ℤ, x = k * π   :=  by sorry
