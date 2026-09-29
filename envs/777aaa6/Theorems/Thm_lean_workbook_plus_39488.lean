-- Prove2me | Theorems.Thm_lean_workbook_plus_39488
-- name    : lean_workbook_plus_39488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/1447aa28-4afd-46ca-9305-eba924229c81
-- statement:
--   Prove that $ x $ is an $ n $ th root of unity if $ x^n=1 $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39488 (n : ℕ) (x : ℂ) : x ^ n = 1 → x ∈ {y : ℂ | y ^ n = 1}   :=  by sorry
