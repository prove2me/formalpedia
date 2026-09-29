-- Prove2me | Theorems.Thm_lean_workbook_plus_38747
-- name    : lean_workbook_plus_38747
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a3c1e8b5-b3a3-455a-b22b-2d3fdcc40f76
-- statement:
--   Let $ x\in R $ such that $ x^{5}-x^{3}+x-17=0 $ . Prove that $ 4< x^{3}< 17 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38747 (x : ℝ) (hx : x^5 - x^3 + x - 17 = 0) : 4 < x^3 ∧ x^3 < 17   :=  by sorry
