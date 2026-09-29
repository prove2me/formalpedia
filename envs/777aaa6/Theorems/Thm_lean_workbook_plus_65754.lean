-- Prove2me | Theorems.Thm_lean_workbook_plus_65754
-- name    : lean_workbook_plus_65754
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6ba769de-6dda-4cef-b168-6f4237a2557b
-- statement:
--   Prove that if $x > y$ is not possible, then $x \leq y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65754 (x y : ℝ) (h : ¬ x > y) : x ≤ y   :=  by sorry
