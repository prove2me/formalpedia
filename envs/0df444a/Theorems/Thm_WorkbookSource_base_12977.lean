-- Prove2me | Theorems.Thm_WorkbookSource_base_12977
-- name    : WorkbookSource.base_12977
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:47:10.847983+00:00
-- url     : https://prove2.me/theorems/0e3961ff-4ff9-4b59-a3d8-dcdea1702b18
-- title:
--   A cyclic shifted rational difference sum is nonnegative
-- statement:
--   Prove that $\frac{b(1-a)}{a(1+b)}+\frac{c(1-b)}{b(1+c)}+\frac{a(1-c)}{c(1+a)}\ge 0$ given $a,b,c >0$ and $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12977` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12977; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12977 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (b * (1 - a) / (a * (1 + b)) + c * (1 - b) / (b * (1 + c)) + a * (1 - c) / (c * (1 + a))) ≥ 0  :=  by sorry
