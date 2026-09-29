-- Prove2me | Theorems.Thm_lean_workbook_plus_16973
-- name    : lean_workbook_plus_16973
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3a9a2066-dcf4-4499-a6e8-0cc466822e04
-- statement:
--   Determine $ ax ^ 5 + by ^ 5 $ if the real numbers a, b, x and y satisfy the equations $ ax + by = 1, ax ^ 2 + by ^ 2 = 2, ax ^ 3 + by ^ 3 = 5, ax ^ 4 + by ^ 4 = 6 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16973 (a b x y : ℝ) (h₁ : a * x + b * y = 1) (h₂ : a * x ^ 2 + b * y ^ 2 = 2) (h₃ : a * x ^ 3 + b * y ^ 3 = 5) (h₄ : a * x ^ 4 + b * y ^ 4 = 6) : a * x ^ 5 + b * y ^ 5 = 41   :=  by sorry
