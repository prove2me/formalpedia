-- Prove2me | Theorems.Thm_lean_workbook_plus_21137
-- name    : lean_workbook_plus_21137
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/86aa2801-11ed-4a8b-a970-938d4ec5acff
-- statement:
--   Prove: $\sin^3 10^{\circ}=\frac{1}{4}(3\sin 10^{\circ}-\sin 30^{\circ})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21137 : sin (10 : ℝ) ^ 3 = 1 / 4 * (3 * sin 10 - sin 30)   :=  by sorry
