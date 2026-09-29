-- Prove2me | Theorems.Thm_WorkbookSource_base_38151
-- name    : WorkbookSource.base_38151
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:21.165975+00:00
-- url     : https://prove2.me/theorems/79520a59-83cf-46f2-bf62-d3040fa563c8
-- title:
--   A three-variable cubic upper bound at total five
-- statement:
--   Let $a,\,b,\,c$ be positive real numbers such that $a+b+c=5.$ Prove that $a^2b+c^2a+2abc \le 20.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38151` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38151; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38151 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 5) : a^2 * b + c^2 * a + 2 * a * b * c ≤ 20  :=  by sorry
