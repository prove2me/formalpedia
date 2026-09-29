-- Prove2me | Theorems.Thm_lean_workbook_plus_1550
-- name    : lean_workbook_plus_1550
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/9b495279-2056-4c8d-a03d-15d810b6abcc
-- statement:
--   Show that for any real number $x$ : \n $ x^2 \sin{x} + x \cos{x} + x^2 + \frac{1}{2} > 0 . $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1550 (x : ℝ) :  x ^ 2 * Real.sin x + x * Real.cos x + x ^ 2 + 1 / 2 > 0   :=  by sorry
