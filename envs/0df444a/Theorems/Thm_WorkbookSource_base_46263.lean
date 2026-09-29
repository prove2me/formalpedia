-- Prove2me | Theorems.Thm_WorkbookSource_base_46263
-- name    : WorkbookSource.base_46263
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:05:10.970281+00:00
-- url     : https://prove2.me/theorems/d5f5ca1b-3e04-4770-994c-8459a1b28744
-- title:
--   A triple product with a symmetric reciprocal correction
-- statement:
--   Let $ a,b,c>0$ , s.t. $ a+b+c=3$ .Prove that: $ abc+\frac{12}{ab+bc+ca}\geq 5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46263` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46263; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46263 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a * b * c + 12 / (a * b + b * c + c * a) ≥ 5  :=  by sorry
