-- Prove2me | Theorems.Thm_lean_workbook_plus_13371
-- name    : lean_workbook_plus_13371
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0ffa9eb9-a9e2-4c77-8aa2-99d8542ae5d7
-- statement:
--   Prove $\left ( {\frac{a+b}{2}} \right )^2 > ab, \quad a \ne b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13371 (a b : ℝ) (hab : a ≠ b) : (a + b) ^ 2 / 4 > a * b   :=  by sorry
