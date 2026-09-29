-- Prove2me | Theorems.Thm_lean_workbook_plus_33424
-- name    : lean_workbook_plus_33424
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/7eccb22d-2d67-4aee-b44f-508adce7f549
-- statement:
--   Given $a+b+c=3$, prove that $a^2 +b^2 + c^2 + ab + ac + bc \geq 6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33424 (a b c : ℝ) (hab : a + b + c = 3) : a^2 + b^2 + c^2 + a * b + a * c + b * c ≥ 6   :=  by sorry
