-- Prove2me | Theorems.Thm_lean_workbook_plus_50179
-- name    : lean_workbook_plus_50179
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/3a2d0f1a-731a-4116-b159-47dcca460f8c
-- statement:
--   Prove that $a^3+b^3+c^3+a^2b+b^2c+c^2a\ge 2(a^2c+c^2b+b^2a)$ for $a,b,c>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50179 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + a^2 * b + b^2 * c + c^2 * a ≥ 2 * (a^2 * c + c^2 * b + b^2 * a)   :=  by sorry
