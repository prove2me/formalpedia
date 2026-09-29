-- Prove2me | Theorems.Thm_lean_workbook_plus_34867
-- name    : lean_workbook_plus_34867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f5d07e7f-1b4c-4d46-8413-fcab040324c7
-- statement:
--   Let $a+b = k$. $ab = \frac{(a+b)^2-(a^2+b^2)}{2} = \frac{k^2-2}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34867 (a b k : ℤ) (h₁ : a + b = k) (h₂ : a * b = (k^2 - 2) / 2) : a * b = (k^2 - 2) / 2   :=  by sorry
