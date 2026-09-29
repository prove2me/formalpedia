-- Prove2me | Theorems.Thm_lean_workbook_plus_24072
-- name    : lean_workbook_plus_24072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/b2a71162-11db-4830-865f-2dbb37619e7d
-- statement:
--   Prove that $\max(\min(a,b),\min(a,c))+\max(a,\min(b,c)) \leq a+\max(b,c)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24072 (a b c : ℝ) : (max (min a b) (min a c)) + max a (min b c) ≤ a + max b c   :=  by sorry
