-- Prove2me | Theorems.Thm_lean_workbook_plus_9474
-- name    : lean_workbook_plus_9474
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/630de73f-1df7-425b-82d4-955eedc962f1
-- statement:
--   Prove that $A^{3}+B^{3}+C^{3}=3ABC$ if $A+B+C=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9474 (A B C : ℂ) (h : A + B + C = 0) : A^3 + B^3 + C^3 = 3 * A * B * C   :=  by sorry
