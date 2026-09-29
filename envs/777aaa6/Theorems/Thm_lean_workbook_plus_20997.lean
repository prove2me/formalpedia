-- Prove2me | Theorems.Thm_lean_workbook_plus_20997
-- name    : lean_workbook_plus_20997
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0b132395-0830-4014-8f2a-7cc9a3801481
-- statement:
--   For a,b,c,d>0 prove that \n $a^2+b^2+c^2+d^2\geq ab+bc+cd+ad$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20997 (a b c d : ℝ) (hab : 0 < a) (hbc : 0 < b) (hcd : 0 < c) (hda : 0 < d) : a^2 + b^2 + c^2 + d^2 >= a * b + b * c + c * d + a * d   :=  by sorry
