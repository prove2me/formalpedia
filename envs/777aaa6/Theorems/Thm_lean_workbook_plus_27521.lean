-- Prove2me | Theorems.Thm_lean_workbook_plus_27521
-- name    : lean_workbook_plus_27521
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/16211a9d-8dab-48e6-bf38-a604637cbade
-- statement:
--   3) $\cosh(\ln a)=\frac{1}{2}\left( a+\frac{1}{a}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27521 : ∀ a > 0, Real.cosh (Real.log a) = (a + 1/a) / 2   :=  by sorry
