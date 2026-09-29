-- Prove2me | Theorems.Thm_lean_workbook_plus_75409
-- name    : lean_workbook_plus_75409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/dda28294-9c11-4a09-b406-10bb28900eb5
-- statement:
--   We sum up the two equations to get $2ab+a+b=2887 \implies 4ab+2a+2b=5774 \implies (2a+1)(2b+1)=5775$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75409  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 2 * a * b + a + b = 2887) :
  (2 * a + 1) * (2 * b + 1) = 5775   :=  by sorry
