-- Prove2me | Theorems.Thm_lean_workbook_plus_3776
-- name    : lean_workbook_plus_3776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/f7da73e6-9cdf-44ae-a284-bf1bcdd868b1
-- statement:
--   $w + z = 1$ , $wz = -3$ , hence $w,z$ are roots of $x^2 - x - 3 = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3776 (w z : ℂ) (hw : w + z = 1) (hz : w * z = -3) : w^2 - w - 3 = 0 ∧ z^2 - z - 3 = 0   :=  by sorry
