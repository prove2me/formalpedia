-- Prove2me | Theorems.Thm_lean_workbook_plus_10076
-- name    : lean_workbook_plus_10076
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/f6f616df-2fb0-48c0-8e78-de3a34adf2d2
-- statement:
--   Prove that $ x^6+2-(x^3+x^2+x)\geq 0$ for $x > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10076 (x : ℝ) (hx : 0 < x) : x ^ 6 + 2 - (x ^ 3 + x ^ 2 + x) ≥ 0   :=  by sorry
