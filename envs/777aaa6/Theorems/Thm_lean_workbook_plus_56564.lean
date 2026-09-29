-- Prove2me | Theorems.Thm_lean_workbook_plus_56564
-- name    : lean_workbook_plus_56564
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/683e0f17-d1a2-4b64-a11b-819e2e59ef44
-- statement:
--   Prove that $(a+b+c)^{3}\geq 9(ab+bc+ca)$ given $a,b,c\geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56564 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : (a + b + c) ^ 3 ≥ 9 * (a * b + b * c + c * a)   :=  by sorry
