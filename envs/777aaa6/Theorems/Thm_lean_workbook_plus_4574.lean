-- Prove2me | Theorems.Thm_lean_workbook_plus_4574
-- name    : lean_workbook_plus_4574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d79d1723-8439-4260-9b41-5dae85ece62c
-- statement:
--   If $x$ is odd, prove that $x^2+1$ is even but not divisible by 4.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4574 (x : ℤ) (h : x % 2 = 1) : (x ^ 2 + 1) % 2 = 0 ∧ (x ^ 2 + 1) % 4 ≠ 0   :=  by sorry
