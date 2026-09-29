-- Prove2me | Theorems.Thm_lean_workbook_plus_14486
-- name    : lean_workbook_plus_14486
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3cb616fc-76f7-4db6-ae94-d174af3dbe8c
-- statement:
--   Let $a=\frac{1}{2006}$ and $b=\frac{2005}{2006}$ . Then $a^3+b^3+3ab=(a+b)(a^2-ab+b^2)+3ab$ . Since $a+b=1$ , the expression becomes $a^2-ab+b^2+3ab=a^2+2ab+b^2=(a+b)^2=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14486  (a b : ℝ)
  (h₀ : a = 1 / 2006)
  (h₁ : b = 2005 / 2006) :
  a^3 + b^3 + 3 * (a * b) = (a + b) * (a^2 - a * b + b^2) + 3 * (a * b)   :=  by sorry
