-- Prove2me | Theorems.Thm_lean_workbook_plus_27782
-- name    : lean_workbook_plus_27782
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/1fb06fe7-474a-4d1c-8ae8-f5ae0063d660
-- statement:
--   B. \n\n $(log_{a}b)(log_{b}c)=log_{a}c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27782 (a b c : ℝ) (ha : 0 < a ∧ 0 < b ∧ 0 < c) (hab : a ≠ 1) (hbc : b ≠ 1) (hca : c ≠ 1) : Real.logb a b * Real.logb b c = Real.logb a c   :=  by sorry
