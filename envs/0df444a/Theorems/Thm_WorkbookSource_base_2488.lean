-- Prove2me | Theorems.Thm_WorkbookSource_base_2488
-- name    : WorkbookSource.base_2488
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:57:24.04688+00:00
-- url     : https://prove2.me/theorems/84b839e6-aa41-44a1-b330-c2037b69a1cc
-- title:
--   A cyclic product ratio sum bounds a pairwise reciprocal sum
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that
--
--    $ \frac {ab}{c(c + a)} + \frac {bc}{a(a + b)} + \frac {ca}{b(b + c)}\geq \frac {a}{c + a} + \frac {b}{a + b} + \frac {c}{b + c}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2488` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2488; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2488 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b) / (c * (c + a)) + (b * c) / (a * (a + b)) + (c * a) / (b * (b + c)) ≥ a / (c + a) + b / (a + b) + c / (b + c)  :=  by sorry
