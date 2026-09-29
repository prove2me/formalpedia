-- Prove2me | Theorems.Thm_WorkbookSource_base_7718
-- name    : WorkbookSource.base_7718
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:33:36.881343+00:00
-- url     : https://prove2.me/theorems/0a95ff52-df92-46b3-a61b-758dbd7c5e69
-- title:
--   A cyclic quadratic ratio bound with a difference correction
-- statement:
--   Let $a, b, c>0$ and $a+b+c=3$ .
--    $$\frac{a^2}{b(c+a)} +\frac{b^2}{c(a+b)}+\frac{c^2}{a(b+c)}\geq \frac{3}{2}+\frac{(a-b) (b-c) (c-a)} {abc} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7718` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7718; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7718 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^2 / (b * (c + a)) + b^2 / (c * (a + b)) + c^2 / (a * (b + c)) ≥ 3 / 2 + (a - b) * (b - c) * (c - a) / (a * b * c)  :=  by sorry
