-- Prove2me | Theorems.Thm_lean_workbook_plus_61442
-- name    : lean_workbook_plus_61442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/270a71bd-1dab-4bc8-b53f-01913494d681
-- statement:
--   Note that if $a,b>0$ , then $|a-b|<max(|a|,|b|)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61442 (a b : ℝ) (hab : a > 0 ∧ b > 0) : |a - b| < max (|a|) (|b|)   :=  by sorry
