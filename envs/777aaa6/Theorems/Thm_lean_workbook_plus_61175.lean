-- Prove2me | Theorems.Thm_lean_workbook_plus_61175
-- name    : lean_workbook_plus_61175
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2812c185-2e34-47e0-9137-32d8a5b97f68
-- statement:
--   Find the integral part of $ 3.999....$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61175 (x : ℝ) (hx : x = 3.999) : ∃ y, y = ⌊x⌋   :=  by sorry
