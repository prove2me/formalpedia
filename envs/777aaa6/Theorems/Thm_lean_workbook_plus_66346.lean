-- Prove2me | Theorems.Thm_lean_workbook_plus_66346
-- name    : lean_workbook_plus_66346
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/85f238fe-6427-4f31-aecb-d3d7830f0e80
-- statement:
--   Prove that $2^n$ is even for all integers $n>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66346 (n : ℕ) (h : n > 0) : Even (2 ^ n)   :=  by sorry
