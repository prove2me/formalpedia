-- Prove2me | Theorems.Thm_lean_workbook_plus_64739
-- name    : lean_workbook_plus_64739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/eae9783d-1e44-4912-972b-65af5a2e4a67
-- statement:
--   Use induction to show $(1-x)^n \geq 1-nx$ for all real number $x \leq 1$ and all $n \in \mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64739 (n : ℕ) (x : ℝ) (hx: x ≤ 1) : (1 - x)^n ≥ 1 - n*x   :=  by sorry
