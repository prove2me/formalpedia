-- Prove2me | Theorems.Thm_lean_workbook_plus_79469
-- name    : lean_workbook_plus_79469
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/9b92d34b-ced8-41d0-a3ff-5e0dc4430c15
-- statement:
--   Prove that for all $a,b>1$ , $2(ab+1)>(a+1)(b+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79469 (a b : ℝ) (hab : 1 < a ∧ 1 < b) : 2 * (a * b + 1) > (a + 1) * (b + 1)   :=  by sorry
