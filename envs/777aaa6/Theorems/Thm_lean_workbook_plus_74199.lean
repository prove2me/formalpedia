-- Prove2me | Theorems.Thm_lean_workbook_plus_74199
-- name    : lean_workbook_plus_74199
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/894a5718-af81-4ba1-a94c-0145db103ea7
-- statement:
--   Derive $sin^2a=\frac{1}{2}(1-cos(2a))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74199 (a : ℝ) : (sin a)^2 = (1 - cos (2 * a)) / 2   :=  by sorry
