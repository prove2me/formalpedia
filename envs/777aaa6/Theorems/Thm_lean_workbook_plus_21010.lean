-- Prove2me | Theorems.Thm_lean_workbook_plus_21010
-- name    : lean_workbook_plus_21010
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/240ae2ce-bb26-44f9-abb7-2d5af331e3ec
-- statement:
--   Assuming that $a$ and $b$ are positive, show that if $a+b-1<ab<1$ , then $a<1$ and $b<1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21010 (a b : ℝ) (hab : a + b - 1 < a * b) (h : a * b < 1) : a < 1 ∧ b < 1   :=  by sorry
