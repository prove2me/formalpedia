-- Prove2me | Theorems.Thm_lean_workbook_plus_22634
-- name    : lean_workbook_plus_22634
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/00bba16b-9dda-416e-a271-86b70d9d98fe
-- statement:
--   If $y_1, y_2$ are two distinct real roots of this equation, we get : $y_1^3-\frac{y_1}4=y_2^3-\frac{y_2}4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22634 (y1 y2 : ℝ) (hy1 : y1 ≠ y2) (h1 : y1^3 - y1 / 4 = y2^3 - y2 / 4) : y1^3 - y2^3 = y1 / 4 - y2 / 4   :=  by sorry
