-- Prove2me | Theorems.Thm_lean_workbook_plus_36144
-- name    : lean_workbook_plus_36144
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/1ce87f9b-91f8-453a-9ec4-daf6d22d8685
-- statement:
--   For positive real numbers $a,b,c$ , prove that $(a^{2}+b^{2})^{2}\geq (a+b+c)(a+b-c)(a+c-b)(b+c-a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36144 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (a + c - b) * (b + c - a)   :=  by sorry
