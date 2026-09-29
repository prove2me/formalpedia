-- Prove2me | Theorems.Thm_lean_workbook_plus_8562
-- name    : lean_workbook_plus_8562
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/46ff52ca-112b-4973-bfdb-2df4af04c685
-- statement:
--   Prove that $a^{x} \times a^{y} = a^{x+y}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8562 (a x y : ℝ) (ha : 0 < a) : a^x * a^y = a^(x + y)   :=  by sorry
