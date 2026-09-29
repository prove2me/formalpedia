-- Prove2me | Theorems.Thm_lean_workbook_plus_61806
-- name    : lean_workbook_plus_61806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ce5071a9-6e3c-4743-8b39-bbfb7e213282
-- statement:
--   Análogamente, si definimos $y=b-1$, la condición $b^3-3b^2+5b=5$ es equivalente a $y^3+2y=2$ ...(2)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61806 (b : ℤ) (hb : b^3 - 3 * b^2 + 5 * b = 5) : (b - 1)^3 + 2 * (b - 1) = 2   :=  by sorry
