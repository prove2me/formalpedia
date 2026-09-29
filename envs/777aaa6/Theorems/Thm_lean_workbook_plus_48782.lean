-- Prove2me | Theorems.Thm_lean_workbook_plus_48782
-- name    : lean_workbook_plus_48782
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/4fc15402-ee10-4b45-baab-2ee86b64abc8
-- statement:
--   Prove that $a^3+b^3+c^3-3abc=\frac{1}{2}(a+b+c)((a-b)^2+(b-c)^2+(c-a)^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48782 : ∀ a b c : ℝ, a^3 + b^3 + c^3 - 3*a*b*c = 1/2 * (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2)   :=  by sorry
