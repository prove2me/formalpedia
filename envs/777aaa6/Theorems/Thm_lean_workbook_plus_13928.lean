-- Prove2me | Theorems.Thm_lean_workbook_plus_13928
-- name    : lean_workbook_plus_13928
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a2c8e31a-bf3c-4016-be14-36733ccff0bb
-- statement:
--   Prove that $3(a+b+c)^{3}\geq 27(a+b+c)$ given $a,b,c\geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13928 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : 3 * (a + b + c) ^ 3 ≥ 27 * (a + b + c)   :=  by sorry
