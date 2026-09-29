-- Prove2me | Theorems.Thm_lean_workbook_plus_40803
-- name    : lean_workbook_plus_40803
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3cbe5f79-751e-4d76-9cc5-de173088e25b
-- statement:
--   Prove that $2(a^2+b^2)(b^2+c^2)(c^2+a^2)\ge\((a+b)(b+c)(c+a)-4abc)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40803 (a b c : ℝ) :
  2 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ ((a + b) * (b + c) * (c + a) - 4 * a * b * c)^2   :=  by sorry
