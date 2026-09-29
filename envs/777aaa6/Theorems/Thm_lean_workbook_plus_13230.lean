-- Prove2me | Theorems.Thm_lean_workbook_plus_13230
-- name    : lean_workbook_plus_13230
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/866c2c5c-da2a-4a85-a256-f48558b6045b
-- statement:
--   Prove that \n\n $ \sqrt {\dfrac{a^2 + b^2}{2} + (c - a)(c - b)}\ge\dfrac{a + b}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13230 (a b c : ℝ) : Real.sqrt ((a^2 + b^2)/2 + (c - a)*(c - b)) ≥ (a + b)/2   :=  by sorry
