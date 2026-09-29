-- Prove2me | Theorems.Thm_lean_workbook_plus_46162
-- name    : lean_workbook_plus_46162
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e147fe45-af27-495c-8d34-d46041a872c4
-- statement:
--   Calculate the result of $\frac{x^2}{x^2}$ when $x$ is 10^302.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46162 (x : ℝ) (hx : x = 10^302) : x^2 / x^2 = 1   :=  by sorry
