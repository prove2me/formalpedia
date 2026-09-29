-- Prove2me | Theorems.Thm_lean_workbook_plus_73985
-- name    : lean_workbook_plus_73985
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d6a21391-34dc-43b0-b385-8dd2e596b41b
-- statement:
--   Prove, using calculus, that $x + \ln(1-x) \leq 0$ for all $ x <1$ , with equality if and only if $x=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73985 (x : ℝ) (hx : x < 1) :
  x + Real.log (1 - x) ≤ 0   :=  by sorry
