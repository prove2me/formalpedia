-- Prove2me | Theorems.Thm_lean_workbook_plus_37200
-- name    : lean_workbook_plus_37200
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4d5b6502-857c-400e-98c7-042134116d09
-- statement:
--   prove that:\n$ \frac {4x}{y + z}\leq x(\frac {1}{y} + \frac {1}{z})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37200 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) : 4 * x / (y + z) ≤ x * (1 / y + 1 / z)   :=  by sorry
