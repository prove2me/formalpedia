-- Prove2me | Theorems.Thm_lean_workbook_plus_79341
-- name    : lean_workbook_plus_79341
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/abfae9c2-372a-46b8-934f-c4f19dacf7d4
-- statement:
--   Solve the equation $5z(z+8)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79341 (z : ℂ) : 5 * z * (z + 8) = 0 ↔ z = 0 ∨ z = -8   :=  by sorry
