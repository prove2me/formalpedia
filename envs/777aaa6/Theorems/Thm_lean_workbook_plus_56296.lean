-- Prove2me | Theorems.Thm_lean_workbook_plus_56296
-- name    : lean_workbook_plus_56296
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d18feab0-b837-4579-b813-61e68985c2e6
-- statement:
--   Note that the RHS is just one-tenth of the sum $ S$ . Then, we can write: \n $ 10S-S=1+\dfrac{S}{10} \nRightarrow 9S=\dfrac{10+S}{10} \nRightarrow 90S=10+S \nRightarrow 89S=10 \nRightarrow \boxed{S=\dfrac{10}{89}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56296  (s : ℝ)
  (h₀ : 10 * s - s = 1 + s / 10) :
  s = 10 / 89   :=  by sorry
