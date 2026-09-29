-- Prove2me | Theorems.Thm_lean_workbook_plus_36323
-- name    : lean_workbook_plus_36323
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e8c5ae6e-5554-47e6-8cfa-884681aac2dc
-- statement:
--   Prove that for all real numbers $a,b,c$ \((a^4+b^4+c^4) \ge max((a^3b+b^3c+c^3a),(ab^3+bc^3+ca^3))\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36323 (a b c : ℝ) : (a^4+b^4+c^4) ≥ max (a^3*b+b^3*c+c^3*a) (a*b^3+b*c^3+c*a^3)   :=  by sorry
