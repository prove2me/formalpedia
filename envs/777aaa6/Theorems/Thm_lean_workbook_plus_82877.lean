-- Prove2me | Theorems.Thm_lean_workbook_plus_82877
-- name    : lean_workbook_plus_82877
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.51614+00:00
-- url     : https://prove2.me/theorems/391c8e93-a68d-4f4c-bdb9-536bcdb09960
-- statement:
--   If $x + x^2 + x^3 = 1$ Prove that : $x^6 + x^4 + 3x^2 = 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82877 (x : ℝ) (hx : x + x^2 + x^3 = 1) : x^6 + x^4 + 3*x^2 = 1   :=  by sorry
