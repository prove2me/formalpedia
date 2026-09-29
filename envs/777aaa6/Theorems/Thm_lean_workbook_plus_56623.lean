-- Prove2me | Theorems.Thm_lean_workbook_plus_56623
-- name    : lean_workbook_plus_56623
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/8e46489f-d8cc-4d58-af96-c0ac34a70c0c
-- statement:
--   Let $ a, b,c >0$ . Prove that $a^2+b^2+c^2\geq ab+bc+ca.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56623 (a b c: ℝ) (ha : a>0) (hb : b>0) (hc : c>0) : a^2 + b^2 + c^2 >= a * b + b * c + c * a   :=  by sorry
