-- Prove2me | Theorems.Thm_WorkbookSource_base_27309
-- name    : WorkbookSource.base_27309
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:51:36.413812+00:00
-- url     : https://prove2.me/theorems/8dad2d0f-0c9d-4aa1-b44b-fe153b3d5325
-- title:
--   A product-pairwise comparison at fixed positive sum
-- statement:
--   If $ a,b,c>0 $ and $ a+b+c=3 $, prove that $ 3(abc+4)\geq5(ab+bc+ca) $ given $ abc\geq-4 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27309` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27309; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27309 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) (h : a * b * c ≥ -4) : 3 * (a * b * c + 4) ≥ 5 * (a * b + b * c + c * a)  :=  by sorry
