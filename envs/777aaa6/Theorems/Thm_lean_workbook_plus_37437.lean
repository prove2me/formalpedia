-- Prove2me | Theorems.Thm_lean_workbook_plus_37437
-- name    : lean_workbook_plus_37437
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0fdf4aae-895e-40c5-887a-7e92c07573c1
-- statement:
--   Prove that $ f(x) = 1+x+x^2+x^3+x^4$ has no real zero.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37437 : ¬ ∃ x : ℝ, x^4 + x^3 + x^2 + x + 1 = 0   :=  by sorry
