-- Prove2me | Theorems.Thm_lean_workbook_plus_12593
-- name    : lean_workbook_plus_12593
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/664fc583-d86c-44d7-8ec2-72997ffc4b08
-- statement:
--   Derive $\log_{a}\frac{b}{c}=\log_{a}b-\log_{a}c$ from the known logarithm properties.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12593 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : Real.logb a (b / c) = Real.logb a b - Real.logb a c   :=  by sorry
