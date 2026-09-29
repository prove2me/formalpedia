-- Prove2me | Theorems.Thm_lean_workbook_plus_28011
-- name    : lean_workbook_plus_28011
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/7542121c-2b00-4603-903c-b9f8e978111e
-- statement:
--   Prove or disprove the inequality: $(x^{n+2}+y^{n+2}+z^{n+2})^{2}\geq 3xyz(x^{2n+1}+y^{2n+1}+z^{2n+1})$ for all $x,y,z,n\geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28011 : ∀ x y z n : ℝ, (x ^ (n + 2) + y ^ (n + 2) + z ^ (n + 2)) ^ 2 ≥ 3 * x * y * z * (x ^ (2 * n + 1) + y ^ (2 * n + 1) + z ^ (2 * n + 1))   :=  by sorry
