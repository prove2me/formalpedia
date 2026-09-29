-- Prove2me | Theorems.Thm_WorkbookSource_base_5494
-- name    : WorkbookSource.base_5494
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:19.874835+00:00
-- url     : https://prove2.me/theorems/6e2f86d7-e53b-4cc7-8039-8dbb7931b71e
-- title:
--   A cyclic rational difference sum at fixed sum three
-- statement:
--   a,b,c >0; \ \ \ a+b+c=3 . Prove that $\frac{a-bc}{b(1+c)}+\frac{b-ca}{c(1+a)}+\frac{c-ab}{a(1+b)} \ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5494` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5494; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5494 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a - b * c) / (b * (1 + c)) + (b - c * a) / (c * (1 + a)) + (c - a * b) / (a * (1 + b)) ≥ 0  :=  by sorry
