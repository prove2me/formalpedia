-- Prove2me | Theorems.Thm_lean_workbook_plus_56471
-- name    : lean_workbook_plus_56471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e93f7930-c0d3-4938-b49b-c56136afb933
-- statement:
--   Prove $4(a^{2}+b^{2}+c^{2}+d^{2}) \geq (a+b+c+d)^{2}$ by Cauchy-Schwarz.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56471  (a b c d : ℝ) :
  4 * (a^2 + b^2 + c^2 + d^2) ≥ (a + b + c + d)^2   :=  by sorry
