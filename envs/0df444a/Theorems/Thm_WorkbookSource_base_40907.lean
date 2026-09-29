-- Prove2me | Theorems.Thm_WorkbookSource_base_40907
-- name    : WorkbookSource.base_40907
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:12:35.628814+00:00
-- url     : https://prove2.me/theorems/c76a9c7c-b421-414f-8b18-744e6accfdb5
-- title:
--   A squared quadratic sum bounds a cubic triple-product term
-- statement:
--   Prove that: $27abc(a^{3}+b^{3}+c^{3}) \leq (a^2+b^2+c^2)^2(a+b+c)^{2}$ where $a,b,c \ge 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40907` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40907; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40907 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 27 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 * (a + b + c) ^ 2  :=  by sorry
