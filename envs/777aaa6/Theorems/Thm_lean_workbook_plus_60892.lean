-- Prove2me | Theorems.Thm_lean_workbook_plus_60892
-- name    : lean_workbook_plus_60892
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/d2941d17-1af0-4668-bbc4-7c05f20801a0
-- statement:
--   Prove $(a^2+1)(1-a)+b(3a-2)+b^2\geq 0$ where $a = x + y$ and $b = xy$ with $x, y \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60892 (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : (x + y) ^ 2 + 1 - (x + y) + (3 * (x + y) - 2) * (x * y) + (x * y) ^ 2 ≥ 0   :=  by sorry
