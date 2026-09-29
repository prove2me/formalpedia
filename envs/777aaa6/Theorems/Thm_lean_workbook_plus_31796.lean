-- Prove2me | Theorems.Thm_lean_workbook_plus_31796
-- name    : lean_workbook_plus_31796
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/27ee1f38-f934-47fd-98ab-053159bd9d8f
-- statement:
--   We have that $ab*\frac{a}{b}=a^2>0$ so $ab$ and $\frac{a}{b}$ have the same sign.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31796  (a b : ℝ)
  (h₀ : b ≠ 0)
  (h₁ : a * b * (a / b) > 0) :
  a^2 > 0   :=  by sorry
