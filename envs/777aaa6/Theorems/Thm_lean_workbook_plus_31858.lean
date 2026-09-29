-- Prove2me | Theorems.Thm_lean_workbook_plus_31858
-- name    : lean_workbook_plus_31858
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/966d5c95-fb86-4705-b94b-2ce0eeafde2a
-- statement:
--   Show that $(x^2-x+6)^2 \geq 16(3x-2)$ for $x \geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31858 (x : ℝ) (hx : 2 ≤ x) : (x^2 - x + 6)^2 ≥ 16 * (3 * x - 2)   :=  by sorry
