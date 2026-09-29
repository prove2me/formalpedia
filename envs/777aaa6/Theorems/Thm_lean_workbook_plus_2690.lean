-- Prove2me | Theorems.Thm_lean_workbook_plus_2690
-- name    : lean_workbook_plus_2690
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/5a5a2f3b-1b57-4c98-889a-19563459ecd7
-- statement:
--   From $a^2+b^2+c^2+4ab-2(ab+bc+ca) = (a+b-c)^2 \geqslant 0,$ so $a^2+b^2+c^2+4ab \geqslant 2(ab+bc+ca).$ The equallity hold when $a+b-c=0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2690 (a b c : ℝ) : a^2 + b^2 + c^2 + 4 * a * b ≥ 2 * (a * b + b * c + c * a)   :=  by sorry
