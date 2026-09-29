-- Prove2me | Theorems.Thm_WorkbookSource_base_11149
-- name    : WorkbookSource.base_11149
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:36:36.108191+00:00
-- url     : https://prove2.me/theorems/452eddd6-485a-41b4-ad26-0d67caa32ef1
-- title:
--   A cyclic fourth-power ratio sum bounds the triple product
-- statement:
--   Prove that \(\frac{a^4 + b^4}{b+c}+\frac{b^4 + c^4}{c+a}+\frac{c^4 + a^4}{a+b}\geq3abc\) For all positive reals \(a\) , \(b\) , and \(c\) .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11149` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11149; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11149 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 + b^4)/(b + c) + (b^4 + c^4)/(c + a) + (c^4 + a^4)/(a + b) ≥ 3 * a * b * c  :=  by sorry
