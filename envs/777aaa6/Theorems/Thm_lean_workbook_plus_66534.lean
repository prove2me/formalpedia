-- Prove2me | Theorems.Thm_lean_workbook_plus_66534
-- name    : lean_workbook_plus_66534
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/8dc66932-4ff7-4f5e-aa19-727469718999
-- statement:
--   Prove that for positive reals a, b, and c, the inequality $a^2+b^2+c^2 + (a+b+c)^2 \ge (a+b)^2 + (b+c)^2 + (c+a)^2$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66534 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + b^2 + c^2 + (a + b + c)^2 ≥ (a + b)^2 + (b + c)^2 + (c + a)^2   :=  by sorry
