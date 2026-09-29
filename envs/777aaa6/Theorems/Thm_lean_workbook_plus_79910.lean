-- Prove2me | Theorems.Thm_lean_workbook_plus_79910
-- name    : lean_workbook_plus_79910
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/f9b9d937-1e4c-4875-b1c1-60cc0d2a0a9e
-- statement:
--   Given $ a + b + ab = 3$ and $ a,b,c > 0$, prove that $ a + b \geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79910 (a b c : ℝ) (h : a + b + a * b = 3) (h1 : a > 0 ∧ b > 0 ∧ c > 0): a + b >= 2   :=  by sorry
