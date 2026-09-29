-- Prove2me | Theorems.Thm_lean_workbook_plus_21840
-- name    : lean_workbook_plus_21840
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/52151a4b-9e7d-46de-b75c-8ba644a118ba
-- statement:
--   Suppose $a$ and $b$ are real numbers that satisfy the system of equations\n\n $a+b=9,\na(a-2)+b(b-2)=21.$\n\nWhat is $ab$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21840 (a b : ℝ) (h₁ : a + b = 9) (h₂ : a * (a - 2) + b * (b - 2) = 21) : a * b = 21   :=  by sorry
