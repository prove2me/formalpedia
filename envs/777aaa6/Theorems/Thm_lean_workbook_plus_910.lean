-- Prove2me | Theorems.Thm_lean_workbook_plus_910
-- name    : lean_workbook_plus_910
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/04502748-4e2f-47b2-9b94-2fe94e924fcf
-- statement:
--   LHS-RHS=\n$\frac{1}{2}((a-b)^2(a+b-c)^2+(b-c)^2(b+c-a)^2+(c-a)^2(c+a-b)^2)\geqslant 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_910 {a b c : ℝ} : (1 / 2) * ((a - b) ^ 2 * (a + b - c) ^ 2 + (b - c) ^ 2 * (b + c - a) ^ 2 + (c - a) ^ 2 * (c + a - b) ^ 2) ≥ 0   :=  by sorry
