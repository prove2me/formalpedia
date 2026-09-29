-- Prove2me | Theorems.Thm_lean_workbook_plus_77716
-- name    : lean_workbook_plus_77716
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/399b1cf9-5e37-43aa-b424-23f10e2e875f
-- statement:
--   In triangle $ABC$ ,prove $a/(a+b)+b/(b+c)+c/(c+a)<2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77716 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a / (a + b) + b / (b + c) + c / (c + a) < 2   :=  by sorry
