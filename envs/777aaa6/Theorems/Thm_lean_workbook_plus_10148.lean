-- Prove2me | Theorems.Thm_lean_workbook_plus_10148
-- name    : lean_workbook_plus_10148
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/21d7e076-6ba4-4fff-8bd8-61d90f0995cc
-- statement:
--   If a,b,c $\in R^+$ prove that $2(a^8+b^8)\geq (a^3+b^3)(a^5+b^5)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10148 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 2 * (a^8 + b^8) ≥ (a^3 + b^3) * (a^5 + b^5)   :=  by sorry
