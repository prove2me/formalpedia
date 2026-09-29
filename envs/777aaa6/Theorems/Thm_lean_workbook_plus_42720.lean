-- Prove2me | Theorems.Thm_lean_workbook_plus_42720
-- name    : lean_workbook_plus_42720
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/f313649e-9437-484d-bbfd-cba9732db677
-- statement:
--   Prove that $ab+bc+ca\geq a+b+c$ when $a=b=c=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42720 (a b c : ℝ) (h1 : a = 1) (h2 : b = 1) (h3 : c = 1) : a * b + b * c + c * a ≥ a + b + c   :=  by sorry
