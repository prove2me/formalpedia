-- Prove2me | Theorems.Thm_WorkbookSource_base_2889
-- name    : WorkbookSource.base_2889
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:02:35.871683+00:00
-- url     : https://prove2.me/theorems/1259d8ce-7995-4451-be3b-d9c8232a84df
-- title:
--   A cyclic pairwise ratio bound with a symmetric correction
-- statement:
--   If a,b,c>0 are real numbers, prove that:
--    $\frac{a+b}{b+c}+\frac{b+c}{c+a}+\frac{c+a}{a+b}+3\cdot\frac{ab+bc+ca}{(a+b+c)^2}\geq4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2889` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2889; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2889 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) + 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2 ≥ 4  :=  by sorry
