-- Prove2me | Theorems.Thm_lean_workbook_plus_34941
-- name    : lean_workbook_plus_34941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/18de041b-78de-4bdf-b1f8-e7d8215fa725
-- statement:
--   Prove that $a^3+b^3+c^3-3abc = (a+b+c)(a^2+b^2+c^2-ab-ac-bc)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34941 (a b c : ℝ) : a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*(a^2 + b^2 + c^2 - a*b - a*c - b*c)   :=  by sorry
