-- Prove2me | Theorems.Thm_lean_workbook_plus_31031
-- name    : lean_workbook_plus_31031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6854f361-889b-4cd7-af4f-4e5e7110f004
-- statement:
--   If real numbers $ a,b \in [0,1]$ , is $ a+b-ab \in [0,1]$ ? explain.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31031 (a b : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) : a + b - a * b ∈ Set.Icc 0 1   :=  by sorry
