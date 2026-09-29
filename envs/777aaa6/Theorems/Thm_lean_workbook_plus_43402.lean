-- Prove2me | Theorems.Thm_lean_workbook_plus_43402
-- name    : lean_workbook_plus_43402
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/8dc0ed97-25e8-4de0-b83d-5b7dcb10ae97
-- statement:
--   So the condition actually is the equality case of AM-GM. So all of its variables $ \frac ab; \frac bc;\frac ca$ are equal. (and, equal to $ 1$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43402  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b + c = 1)
  (h₂ : a / b = b / c)
  (h₃ : b / c = c / a) :
  a / b = 1 ∧ b / c = 1 ∧ c / a = 1   :=  by sorry
