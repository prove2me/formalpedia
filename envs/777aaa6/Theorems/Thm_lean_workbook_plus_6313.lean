-- Prove2me | Theorems.Thm_lean_workbook_plus_6313
-- name    : lean_workbook_plus_6313
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/10830713-641b-4231-9f36-2f84546c2e95
-- statement:
--   Prove that \(a^2+b^2+c^2\ge ab+bc+ca\) given \(a,b,c\) are positive real numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6313 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + a * c   :=  by sorry
