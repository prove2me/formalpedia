-- Prove2me | Theorems.Thm_lean_workbook_plus_63156
-- name    : lean_workbook_plus_63156
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/dd941f06-965b-40f8-b156-0bd8ee2dd05d
-- statement:
--   $=\frac{a+b}{a+b}+\frac{c}{a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63156 (a b c : ℝ) : a / (a + b) + b / (a + b) + c / (a + b) = (a + b + c) / (a + b)   :=  by sorry
