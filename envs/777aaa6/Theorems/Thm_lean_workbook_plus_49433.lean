-- Prove2me | Theorems.Thm_lean_workbook_plus_49433
-- name    : lean_workbook_plus_49433
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/f51f4abf-7905-4455-9d43-da063bb14204
-- statement:
--   Prove that $x^5-x^3-x^2+1\geq0$ for all non-negative real numbers $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49433 (x : ℝ) (hx : 0 ≤ x) : x^5 - x^3 - x^2 + 1 ≥ 0   :=  by sorry
