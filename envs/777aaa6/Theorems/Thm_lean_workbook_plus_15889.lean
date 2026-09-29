-- Prove2me | Theorems.Thm_lean_workbook_plus_15889
-- name    : lean_workbook_plus_15889
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/542ea18d-85f3-4fd4-b438-e7781e6f66f1
-- statement:
--   Let $ \alpha = \frac {1 + \sqrt {5}}{2}$ , $ \beta = \frac {1 - \sqrt {5}}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15889 (α β : ℝ) (h₁ : α = (1 + Real.sqrt 5) / 2) (h₂ : β = (1 - Real.sqrt 5) / 2) : α + β = 1 ∧ α - β = Real.sqrt 5   :=  by sorry
