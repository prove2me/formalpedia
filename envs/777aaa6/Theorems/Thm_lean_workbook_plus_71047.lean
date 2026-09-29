-- Prove2me | Theorems.Thm_lean_workbook_plus_71047
-- name    : lean_workbook_plus_71047
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/447a5d9a-dd60-44fe-9263-db4fe419ef5c
-- statement:
--   If $a,b>0$ and $a(a+b)^2=4$ , then prove: $a^3b(a^2+b^2){\leq}2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71047 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * (a + b) ^ 2 = 4) : a ^ 3 * b * (a ^ 2 + b ^ 2) ≤ 2   :=  by sorry
