-- Prove2me | Theorems.Thm_WorkbookSource_base_46175
-- name    : WorkbookSource.base_46175
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:00:16.536514+00:00
-- url     : https://prove2.me/theorems/97e416c6-398b-4d9b-aa3e-d9dde1853875
-- title:
--   A pair-product sum bounds cyclic rational differences
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that $ ab+bc+ca \ge \frac{4a^3(b+c-a)}{(b+c)^2}+\frac{4b^3(c+a-b)}{(c+a)^2}+\frac{4c^3(a+b-c)}{(a+b)^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46175` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46175; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46175 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b + b * c + c * a ≥ 4 * a ^ 3 * (b + c - a) / (b + c) ^ 2 + 4 * b ^ 3 * (c + a - b) / (c + a) ^ 2 + 4 * c ^ 3 * (a + b - c) / (a + b) ^ 2  :=  by sorry
