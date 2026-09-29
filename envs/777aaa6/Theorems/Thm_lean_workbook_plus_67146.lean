-- Prove2me | Theorems.Thm_lean_workbook_plus_67146
-- name    : lean_workbook_plus_67146
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/593a5d51-0a13-4e20-9c19-d937f8770bf3
-- statement:
--   Prove that if $n$ is not divisible by 3, then $n^2$ is not divisible by 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67146 (n : ℤ) : ¬ 3 ∣ n → ¬ 3 ∣ n^2   :=  by sorry
