-- Prove2me | Theorems.Thm_lean_workbook_plus_36775
-- name    : lean_workbook_plus_36775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3d8eaf9c-831b-4467-9c0e-985fcae51dbf
-- statement:
--   First expand $(a + 1)(b + 1)(c + 1) = (a + b + c) + (ab + ac + bc) + abc + 1$. By Vieta's formulas, $ a + b + c = 0$, $ ab + ac + bc = - 19$, $ abc = - 30$. Plugging in, we have $(a + 1)(b + 1)(c + 1) = 0 + - 19 + - 30 + 1 = \boxed{ - 48}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36775  (a b c : ℂ)
  (h₀ : a + b + c = 0)
  (h₁ : a * b + b * c + c * a = -19)
  (h₂ : a * b * c = -30) :
  (a + 1) * (b + 1) * (c + 1) = -48   :=  by sorry
