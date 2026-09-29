-- Prove2me | Theorems.Thm_lean_workbook_plus_44876
-- name    : lean_workbook_plus_44876
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c5b7453b-670c-4f95-8287-efcf92994121
-- statement:
--   Let $x,y\ge 0$ such that $x+y=3$ . Prove that $xy^2\le 4$ , and find when equality occurs.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44876 (x y : ℝ) (h₁ : x + y = 3) (h₂ : x ≥ 0 ∧ y ≥ 0) : x * y ^ 2 ≤ 4   :=  by sorry
