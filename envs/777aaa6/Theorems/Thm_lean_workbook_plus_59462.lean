-- Prove2me | Theorems.Thm_lean_workbook_plus_59462
-- name    : lean_workbook_plus_59462
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/0c9b40fa-1ae8-4ba8-b9f6-93af4922636e
-- statement:
--   Let $a,b$ be reals such that $(a^2+1)(b^2+1)=4$ . Prove that $(a+1)(b-1)\geq -4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59462 (a b : ℝ) (hab : (a^2 + 1) * (b^2 + 1) = 4) : (a + 1) * (b - 1) ≥ -4   :=  by sorry
