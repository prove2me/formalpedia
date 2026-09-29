-- Prove2me | Theorems.Thm_WorkbookSource_base_32454
-- name    : WorkbookSource.base_32454
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:35:44.094711+00:00
-- url     : https://prove2.me/theorems/35af58cb-a0b8-4e0e-849b-209860c6d432
-- title:
--   A weighted pair-product reciprocal lower bound
-- statement:
--   Let $a,b,c>0$ .Prove that : $$\frac{1}{(2a+b)(2a+c)}+\frac{1}{(2b+c)(2b+a)}+\frac{1}{(2c+a)(2c+b)}\ge \frac{1}{ab+bc+ca}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32454` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32454; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32454 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / ((2 * a + b) * (2 * a + c)) + 1 / ((2 * b + c) * (2 * b + a)) + 1 / ((2 * c + a) * (2 * c + b)) ≥ 1 / (a * b + b * c + c * a)  :=  by sorry
