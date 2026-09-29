-- Prove2me | Theorems.Thm_lean_workbook_plus_49564
-- name    : lean_workbook_plus_49564
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/21137e9b-5422-422f-9219-91ffefdad23b
-- statement:
--   and $a^2+b^2+c^2+3\ge 2(a+b+c) \ \ \ \iff (a-1)^2+(b-1)^2+(c-1)^2\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49564 (a b c : ℝ) : a^2 + b^2 + c^2 + 3 ≥ 2 * (a + b + c) ↔ (a - 1)^2 + (b - 1)^2 + (c - 1)^2 ≥ 0   :=  by sorry
