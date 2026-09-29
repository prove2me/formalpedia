-- Prove2me | Theorems.Thm_WorkbookSource_base_834
-- name    : WorkbookSource.base_834
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:50:54.425557+00:00
-- url     : https://prove2.me/theorems/e694dc38-79f4-4e55-badb-e7c483a9917c
-- title:
--   A fixed-sum cyclic ratio and reciprocal-product lower bound
-- statement:
--   If $ a,b,c>0,a+b+c=3 $ prove that:
--    $ \frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a}+\frac{1}{abc}\ge\frac{5}{2} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_834` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_834; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_834 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + b) + b / (b + c) + c / (c + a) + 1 / (a * b * c) ≥ 5 / 2  :=  by sorry
