-- Prove2me | Theorems.Thm_lean_workbook_plus_63241
-- name    : lean_workbook_plus_63241
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/cf8870a0-d324-49c3-8704-2f86c34c6101
-- statement:
--   Prove that there are infinitely many integers $n$ for which $\cos n \geq 1 - \epsilon$, given $1 > \epsilon > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63241 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) : ∃ n : ℤ, (Real.cos n ≥ 1 - ε)   :=  by sorry
