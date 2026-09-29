-- Prove2me | Theorems.Thm_lean_workbook_plus_14433
-- name    : lean_workbook_plus_14433
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e19e72bc-3ff0-425a-8ab5-e25a37c190a3
-- statement:
--   Prove that $(a-1)^{2}+(b-1)^{2}+(c-1)^{2} = 9$ given $a+b+c=6$ and $ab+bc+ca=9$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14433 (a b c : ℝ) (h₁ : a + b + c = 6) (h₂ : a * b + b * c + c * a = 9) : (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 = 9   :=  by sorry
