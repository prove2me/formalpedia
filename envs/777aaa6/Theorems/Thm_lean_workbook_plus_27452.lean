-- Prove2me | Theorems.Thm_lean_workbook_plus_27452
-- name    : lean_workbook_plus_27452
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/eec86142-595b-451f-8c59-d05295f91289
-- statement:
--   Prove that $\sin(3x) = (1+2\cos(2x))\sin x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27452 (x : ℝ) : Real.sin (3*x) = (1 + 2*Real.cos (2*x))*Real.sin x   :=  by sorry
