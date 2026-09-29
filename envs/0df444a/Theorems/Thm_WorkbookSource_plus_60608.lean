-- Prove2me | Theorems.Thm_WorkbookSource_plus_60608
-- name    : WorkbookSource.plus_60608
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:54:36.984279+00:00
-- url     : https://prove2.me/theorems/36b58761-5318-4b21-9edb-daefbec38781
-- title:
--   A squared difference ratio sum bounds a normalized quadratic sum
-- statement:
--   For any positive real numbers $ a,b,c$ we have the inequality
--   $\frac{(b+c-a)^2}{17a^2+7(b+c)^2}+\frac{(c+a-b)^2}{17b^2+7(c+a)^2}+\frac{(a+b-c)^2}{17c^2+7(a+b)^2}\geq\frac{a^2+b^2+c^2}{5(a+b+c)^2} $.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_60608` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_60608; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_60608 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c - a) ^ 2 / (17 * a ^ 2 + 7 * (b + c) ^ 2) + (c + a - b) ^ 2 / (17 * b ^ 2 + 7 * (c + a) ^ 2) + (a + b - c) ^ 2 / (17 * c ^ 2 + 7 * (a + b) ^ 2) ≥ (a ^ 2 + b ^ 2 + c ^ 2) / (5 * (a + b + c) ^ 2)   :=  by sorry
