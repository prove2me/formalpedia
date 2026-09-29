-- Prove2me | Theorems.Thm_lean_workbook_plus_49098
-- name    : lean_workbook_plus_49098
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0b290603-5364-43b4-afe7-6b0b9c8cb9d2
-- statement:
--   (b) If $ x \neq 0$ and $ xy = x$ then $ y = 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49098 (x y : ℝ) (hx : x ≠ 0) : x * y = x → y = 1   :=  by sorry
