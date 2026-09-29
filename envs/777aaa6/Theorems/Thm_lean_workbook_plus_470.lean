-- Prove2me | Theorems.Thm_lean_workbook_plus_470
-- name    : lean_workbook_plus_470
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/1a63b90a-5986-4d0d-9202-c129840ab5d8
-- statement:
--   Find the sum of the infinite arithmetic series $0+0+0+0...$ when $a=0$ and $d=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_470 (a d : ℝ) (h : a = 0 ∧ d = 0) : ∑' i : ℕ, (a + i * d) = 0   :=  by sorry
