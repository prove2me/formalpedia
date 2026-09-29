-- Prove2me | Theorems.Thm_lean_workbook_plus_24077
-- name    : lean_workbook_plus_24077
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1d98db23-52bb-487e-8d76-43265945fe6f
-- statement:
--   We have the identity $ 2\sin a \sin b=\cos (a-b)-\cos (a+b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24077 (a b : ℝ) : 2 * Real.sin a * Real.sin b = Real.cos (a - b) - Real.cos (a + b)   :=  by sorry
