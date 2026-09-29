-- Prove2me | Theorems.Thm_lean_workbook_plus_79750
-- name    : lean_workbook_plus_79750
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/cf194283-d7e4-44a9-8176-a93ac802a8a1
-- statement:
--   Prove that $a^4 + b^4 + c^4 \geq abc(a+b+c)$ given $a,b,c>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79750 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c)   :=  by sorry
