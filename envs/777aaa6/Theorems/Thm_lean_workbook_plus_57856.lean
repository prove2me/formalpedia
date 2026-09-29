-- Prove2me | Theorems.Thm_lean_workbook_plus_57856
-- name    : lean_workbook_plus_57856
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/4a87b2f8-f2ee-460d-bc8f-1dda2e7dde24
-- statement:
--   Prove that for real nos. $ a,b,c>2$ the relation holds good: $ a+b+c<abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57856 (a b c : ℝ) (h1 : 2 < a) (h2 : 2 < b) (h3 : 2 < c) : a + b + c < a * b * c   :=  by sorry
