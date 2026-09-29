-- Prove2me | Theorems.Thm_lean_workbook_plus_40204
-- name    : lean_workbook_plus_40204
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3842a254-8ffc-4ef9-9bdd-6e5855d2916f
-- statement:
--   Verify the condition $b > a/3$ using the example $x = 1$, $a = 10$, and $b = 4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40204 (x a b : ℝ) (hx : x = 1) (ha : a = 10) (hb : b = 4) : b > a/3   :=  by sorry
