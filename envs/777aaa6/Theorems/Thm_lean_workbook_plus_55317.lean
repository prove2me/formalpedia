-- Prove2me | Theorems.Thm_lean_workbook_plus_55317
-- name    : lean_workbook_plus_55317
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/5fdaf72b-d15f-4694-a5bc-616c9b90094d
-- statement:
--   Given $a+b+c=0$ and $a^2+b^2+c^2=1$, prove that $ab+bc+ca = -\frac{1}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55317 (a b c : ℝ) (h1 : a + b + c = 0) (h2 : a^2 + b^2 + c^2 = 1) : a * b + b * c + c * a = -1 / 2   :=  by sorry
