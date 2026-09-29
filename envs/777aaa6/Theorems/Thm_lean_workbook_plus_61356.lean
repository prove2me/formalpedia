-- Prove2me | Theorems.Thm_lean_workbook_plus_61356
-- name    : lean_workbook_plus_61356
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c5e9d35e-3fcf-437d-a24d-5da056ea2b0c
-- statement:
--   Is $8(a^3+b^3+c^3)<=9(a^2+bc)(b^2+ac)(c^2+ab)$ true for all positive reals $a, b, c$ , $abc=1$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61356 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 8 * (a ^ 3 + b ^ 3 + c ^ 3) ≤ 9 * (a ^ 2 + b * c) * (b ^ 2 + a * c) * (c ^ 2 + a * b)   :=  by sorry
