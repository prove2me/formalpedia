-- Prove2me | Theorems.Thm_lean_workbook_plus_10780
-- name    : lean_workbook_plus_10780
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/24ccbf5a-2976-4561-aaca-75f781f0705b
-- statement:
--   Prove the change-of-base formula: $\log_{a^b}c = \frac{1}{b}\log_{a}c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10780 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Real.logb (a^b) c = (1/b) * Real.logb a c   :=  by sorry
