-- Prove2me | Theorems.Thm_lean_workbook_plus_14023
-- name    : lean_workbook_plus_14023
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/076c9b20-1194-45d2-be14-ce3c4c8d23a0
-- statement:
--   Divide both sides of the equation by $3$ : \n\n$x^2 + 6x + 9 = 0 \Rightarrow\n(x + 3)^2 = 0$ \n\nSo $x = \boxed{-3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14023  (x : ℝ)
  (h₀ : x^2 + 6 * x + 9 = 0) :
  x = -3   :=  by sorry
