-- Prove2me | Theorems.Thm_lean_workbook_plus_420
-- name    : lean_workbook_plus_420
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/7b331ba4-ffae-4cec-b6ba-8250c2ca2e5c
-- statement:
--   Illustrate the solution using the quadratic equation $(x-x_1)(x-x_2)\equiv x^2-Sx+P=0$ where $S=x_1+x_2$ and $P=x_1x_2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_420 (x x1 x2 S P : ℂ) (hx : x ≠ x1 ∧ x ≠ x2) (hS : S = x1 + x2) (hP : P = x1 * x2) : (x - x1) * (x - x2) = x^2 - S * x + P   :=  by sorry
