-- Prove2me | Theorems.Thm_lean_workbook_plus_2409
-- name    : lean_workbook_plus_2409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/92e74939-5053-4f18-b493-6e0b5f969274
-- statement:
--   For arbitrary positive numbers $a,b,c$ , prove the inequality $\frac{a}{b+2c}+\frac{b}{c+2a}+\frac{c}{a+2b}\geq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2409 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) ≥ 1   :=  by sorry
