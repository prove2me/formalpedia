-- Prove2me | Theorems.Thm_lean_workbook_plus_24525
-- name    : lean_workbook_plus_24525
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3fc7e154-bd80-4483-8b63-6645a024a2bd
-- statement:
--   Let $a, b, c$ be positive real numbers which are all less than 1. Prove the following inequality:\na + b + c - abc < 2.\n1956 Tokyo Institute of Technology entrance exam
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24525 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1): a + b + c - a * b * c < 2   :=  by sorry
