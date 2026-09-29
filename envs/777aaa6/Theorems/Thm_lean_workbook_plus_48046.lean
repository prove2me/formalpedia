-- Prove2me | Theorems.Thm_lean_workbook_plus_48046
-- name    : lean_workbook_plus_48046
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d566cc85-7157-418b-a662-070121acc31e
-- statement:
--   Let be $a,b $ be reals such that $a^3b+ab^3=\frac{2}{9}$. Show that $a^2+b^2+ab\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48046 (a b : ℝ) (h : a^3 * b + a * b^3 = 2 / 9) : a^2 + b^2 + a * b ≥ 1   :=  by sorry
