-- Prove2me | Theorems.Thm_lean_workbook_plus_63754
-- name    : lean_workbook_plus_63754
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/060745b0-6e92-4499-a916-b10634cf1c3a
-- statement:
--   prove that $(b+c-a)^2+(c+a-b)^2+(a+b-c)^2>= ab +bc +ca$ for any reals a,b and c
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63754 (a b c: ℝ) : (b + c - a) ^ 2 + (c + a - b) ^ 2 + (a + b - c) ^ 2 >= a * b + b * c + c * a   :=  by sorry
