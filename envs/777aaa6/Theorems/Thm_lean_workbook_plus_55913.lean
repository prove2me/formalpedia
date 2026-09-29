-- Prove2me | Theorems.Thm_lean_workbook_plus_55913
-- name    : lean_workbook_plus_55913
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/24ed1cec-c549-40e7-a502-68b84f0afaf5
-- statement:
--   $x-\frac{x}{2} <x_n<x+\frac{x}{2}<2x \Longrightarrow \boxed{\frac{x}{2}<x_n<2x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55913 : x - x / 2 < x_n ∧ x_n < x + x / 2 ∧ x + x / 2 < 2 * x → x / 2 < x_n ∧ x_n < 2 * x   :=  by sorry
