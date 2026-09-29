-- Prove2me | Theorems.Thm_lean_workbook_plus_54325
-- name    : lean_workbook_plus_54325
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/8c7726d9-7bf2-41c6-b167-65fd8a578aa0
-- statement:
--   Given $ a,b,c > 1$ and $ ab + bc + ca = 2abc$ .Prove that: \n\n $ 5(a + b + c) - 4abc\geq\ 9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54325 (a b c : ℝ) (hab : 1 < a) (hbc : 1 < b) (hca : 1 < c)(habc : a * b * c = 1) : 5 * (a + b + c) - 4 * a * b * c ≥ 9   :=  by sorry
