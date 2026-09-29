-- Prove2me | Theorems.Thm_lean_workbook_plus_5840
-- name    : lean_workbook_plus_5840
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e7354be3-3d9f-42e3-a521-3746aad45f60
-- statement:
--   Prove, without using calculus, that $x + \ln(1-x) \leq 0$ for all $ x <1$ , with equality if and only if $x=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5840 (x : ℝ) (hx : x < 1) : x + Real.log (1 - x) ≤ 0   :=  by sorry
