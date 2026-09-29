-- Prove2me | Theorems.Thm_lean_workbook_plus_42482
-- name    : lean_workbook_plus_42482
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/acbaff02-2e17-4bd0-af39-c239b54c5dc1
-- statement:
--   Prove that $3 \sin a - \sin 3a = 2 \sin a (1- \cos 2a)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42482 (a : ℝ) : 3 * Real.sin a - Real.sin (3*a) = 2 * Real.sin a * (1 - Real.cos (2*a))   :=  by sorry
