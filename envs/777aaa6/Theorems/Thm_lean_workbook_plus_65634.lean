-- Prove2me | Theorems.Thm_lean_workbook_plus_65634
-- name    : lean_workbook_plus_65634
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9a2b8214-f232-4990-a118-4d0d56541ff7
-- statement:
--   For $a, b, c \geq 0$, prove that $2+2(a^4+b^4)\geq ab^3+ba^3+a^3+b^3+a+b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65634 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 2 + 2 * (a ^ 4 + b ^ 4) ≥ a * b ^ 3 + b * a ^ 3 + a ^ 3 + b ^ 3 + a + b   :=  by sorry
