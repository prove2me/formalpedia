-- Prove2me | Theorems.Thm_lean_workbook_plus_49730
-- name    : lean_workbook_plus_49730
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ad9a8cee-97b6-446c-bf20-982843666933
-- statement:
--   $sin(x-y)sin(z-x)=\frac { 1 }{ 2 } [cos(2x-y-z)-cos(z-y)]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49730 (x y z : ℝ) : Real.sin (x - y) * Real.sin (z - x) = 1/2 * (Real.cos (2 * x - y - z) - Real.cos (z - y))   :=  by sorry
