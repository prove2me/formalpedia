-- Prove2me | Theorems.Thm_lean_workbook_plus_64280
-- name    : lean_workbook_plus_64280
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d3fecde4-44c7-4322-a20a-07d24b448a2e
-- statement:
--   Prove that at least one among $a_{1},a_{2},a_{3},...,a_{n}$ is less than $1$ given $a_{1}+a_{2}+a_{3}+...+a_{n}<n$ for positive real numbers $a_{1},a_{2},a_{3},...,a_{n}$ and a positive integer $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64280 (n : ℕ) (a : Fin n → ℝ) (h : ∑ i, a i < n) : ∃ i, a i < 1   :=  by sorry
