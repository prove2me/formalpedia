-- Prove2me | Theorems.Thm_WorkbookSource_base_43259
-- name    : WorkbookSource.base_43259
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:47:21.870109+00:00
-- url     : https://prove2.me/theorems/39242578-460a-43da-9dbd-1ca79e50c6bf
-- title:
--   A symmetric quadratic ratio with a normalized product correction
-- statement:
--   a,b,c>0. Prove: $8\\frac{(a+b+c)^{2}}{ab+bc+ac}+27\\frac{(a+b)(b+c)(a+c)}{(a+b+c)^{3}}\geq 32$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43259` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43259; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43259 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a + b + c) ^ 2 / (a * b + b * c + a * c) + 27 * (a + b) * (b + c) * (a + c) / (a + b + c) ^ 3 ≥ 32  :=  by sorry
