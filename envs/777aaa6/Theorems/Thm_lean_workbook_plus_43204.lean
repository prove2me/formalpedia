-- Prove2me | Theorems.Thm_lean_workbook_plus_43204
-- name    : lean_workbook_plus_43204
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/8bf21640-c19f-48c2-b10c-babdcde6a79f
-- statement:
--   $(2x - 1)(x - 2) = 0$ . So $ x = \frac {1}{2}$ or $ 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43204  (x : ℝ)
  (h₀ : (2 * x - 1) * (x - 2) = 0) :
  x = 1 / 2 ∨ x = 2   :=  by sorry
