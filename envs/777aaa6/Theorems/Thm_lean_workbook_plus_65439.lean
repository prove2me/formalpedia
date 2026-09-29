-- Prove2me | Theorems.Thm_lean_workbook_plus_65439
-- name    : lean_workbook_plus_65439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/23354977-942e-46ce-85eb-ee427f74771d
-- statement:
--   Which gives $2(3-\sqrt{5})\leq k\leq 2(3+\sqrt{5})$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65439 (k : ℝ) (h₁ : 0 < k) (h₂ : 2 * (3 - Real.sqrt 5) ≤ k) (h₃ : k ≤ 2 * (3 + Real.sqrt 5)) : 2 * (3 - Real.sqrt 5) ≤ k ∧ k ≤ 2 * (3 + Real.sqrt 5)   :=  by sorry
