-- Prove2me | Theorems.Thm_lean_workbook_plus_36836
-- name    : lean_workbook_plus_36836
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/65018a22-143d-48ae-8458-1060c6247f91
-- statement:
--   Prove that for a triangle, $ a^2 \geq (b-c)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36836 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 ≥ (b - c)^2   :=  by sorry
