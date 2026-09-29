-- Prove2me | Theorems.Thm_lean_workbook_plus_66037
-- name    : lean_workbook_plus_66037
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/70ca9d59-6231-450a-a2a5-8d0e0a4a24f4
-- statement:
--   How many all triple $(x, y, z)$ of Positive Integers satisfy the equation: $xyz=400$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66037 (x y z : ℕ) (h : x*y*z = 400) : x*y*z = 400 ∧ x > 0 ∧ y > 0 ∧ z > 0   :=  by sorry
