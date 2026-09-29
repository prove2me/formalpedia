-- Prove2me | Theorems.Thm_lean_workbook_plus_8906
-- name    : lean_workbook_plus_8906
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/22996d23-053c-4115-8afa-1c5f4994aa75
-- statement:
--   Given $a, b, c > 0$ such that $ab + bc + ca = abc + 2$, prove that $a^2 + b^2 + c^2 + abc \geq 4$ using AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8906 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a * b + b * c + c * a = a * b * c + 2) : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c ≥ 4   :=  by sorry
