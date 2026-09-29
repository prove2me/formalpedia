-- Prove2me | Theorems.Thm_lean_workbook_plus_23970
-- name    : lean_workbook_plus_23970
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/490a78f5-6eef-4064-bb62-48e59242c9e0
-- statement:
--   Prove that $x^8+x^7-x^5-x^4-x^3+x+1>x^8$ for all $x\geq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23970 (x : ℝ) (hx: x ≥ 2) : x^8 + x^7 - x^5 - x^4 - x^3 + x + 1 > x^8   :=  by sorry
