-- Prove2me | Theorems.Thm_lean_workbook_plus_14321
-- name    : lean_workbook_plus_14321
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/931f404f-96e1-405a-a310-32d0e644058f
-- statement:
--   Using AM-GM inequality, prove that if $a + b = 4$, then $ab \leq 4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14321 (a b : ℝ) (h : a + b = 4) : a * b ≤ 4   :=  by sorry
