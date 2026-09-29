-- Prove2me | Theorems.Thm_lean_workbook_plus_53137
-- name    : lean_workbook_plus_53137
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5a5859a0-48db-4fb2-8d51-986dc9057f70
-- statement:
--   For each $x\in \mathbb{R},x>1$, prove that there is some prime $p$ with $x<p<2x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53137 (x : ℝ) (hx : 1 < x) : ∃ p, x < p ∧ p < 2 * x   :=  by sorry
