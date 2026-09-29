-- Prove2me | Theorems.Thm_lean_workbook_plus_25971
-- name    : lean_workbook_plus_25971
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/76921e4e-f202-4931-bc57-6d16a8c3049c
-- statement:
--   But then $x^2 - x - 1 = 0 \implies x = \frac{1 \pm \sqrt{5}}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25971  (x : ℝ)
  (h₀ : x^2 - x - 1 = 0) :
  x = (1 + Real.sqrt 5) / 2 ∨ x = (1 - Real.sqrt 5) / 2   :=  by sorry
