-- Prove2me | Theorems.Thm_lean_workbook_plus_12307
-- name    : lean_workbook_plus_12307
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d3d244e3-8987-487b-8094-8861bf9751a7
-- statement:
--   Prove that $a_{n} > 2$ for all positive integers, given the sequence defined by $a_{n+1} = \sqrt{2+a_{n}}$ and $a_{1}=3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12307 (n : ℕ) (a : ℕ → ℝ) (a1 : a 0 = 3) (a_rec : ∀ n, a (n + 1) = Real.sqrt (2 + a n)) : ∀ n, a n > 2   :=  by sorry
