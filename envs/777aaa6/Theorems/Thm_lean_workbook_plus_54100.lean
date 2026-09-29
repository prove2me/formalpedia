-- Prove2me | Theorems.Thm_lean_workbook_plus_54100
-- name    : lean_workbook_plus_54100
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/53d0062f-84dd-4e95-bdff-0e378e4226b3
-- statement:
--   The maximum is neither $ 2$ nor $ 3$ . It is a number in $ (2,3)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54100  (x : ℝ)
  (h₀ : 2 < x)
  (h₁ : x < 3)
  (h₂ : 0 < x) :
  2 < x ∧ x < 3   :=  by sorry
