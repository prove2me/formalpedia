-- Prove2me | Theorems.Thm_lean_workbook_plus_29909
-- name    : lean_workbook_plus_29909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9bc92724-aa29-4fe3-a6c8-0750c650a8c0
-- statement:
--   You only need here is $|\,|x|-|y|\,| \le |x-y|,$ which is easily verified by squaring both sides.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29909 (x y : ℝ) : |(abs x) - (abs y)| ≤ abs (x - y)   :=  by sorry
