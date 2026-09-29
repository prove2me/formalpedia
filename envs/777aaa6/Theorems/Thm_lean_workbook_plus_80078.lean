-- Prove2me | Theorems.Thm_lean_workbook_plus_80078
-- name    : lean_workbook_plus_80078
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/0a25d18a-222c-4e3e-acae-f2ec9b6e8ca0
-- statement:
--   Prove that if $x = y$ , then $ax = ay$ for arbitrary $a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80078 (a x y : ℝ) (h : x = y) : a * x = a * y   :=  by sorry
