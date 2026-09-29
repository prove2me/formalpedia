-- Prove2me | Theorems.Thm_lean_workbook_plus_30749
-- name    : lean_workbook_plus_30749
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/80507717-bb03-4fff-940b-5efcc8bfa025
-- statement:
--   Theorem: Suppose $a$ and $b$ are real numbers with $a<b.$ Then there exists a rational number $q$ such that $a<q<b.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30749 (a b : ℝ) (hab : a < b) : ∃ q : ℚ, a < q ∧ ↑q < b   :=  by sorry
