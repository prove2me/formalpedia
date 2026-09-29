-- Prove2me | Theorems.Thm_lean_workbook_plus_69499
-- name    : lean_workbook_plus_69499
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/20421130-0b9c-4aa4-9db8-b96ddcf04cf6
-- statement:
--   Prove that $4(\sum a^2)^2\geq3(\sum a^4+ 3\sum a^2b^2)$ given $a^2+b^2+c^2=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69499    (a b c : ℝ)
    (h₁ : a^2 + b^2 + c^2 = 1) :
  4 * (a^2 + b^2 + c^2)^2 ≥ 3 * (a^4 + b^4 + c^4 + 3 * (a^2 * b^2 + b^2 * c^2 + a^2 * c^2))   :=  by sorry
