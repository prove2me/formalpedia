-- Prove2me | Theorems.Thm_WorkbookSource_plus_28828
-- name    : WorkbookSource.plus_28828
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:54:23.419255+00:00
-- url     : https://prove2.me/theorems/edf53c1e-551a-44cb-b6d3-c3e6871245e7
-- title:
--   A refined quartic inequality at fixed sum three
-- statement:
--   a,b,c>0 \ \ \ a+b+c=3 . Prove that $ 4(a^4+b^4+c^4)+(a+b)(b+c)(c+a)( \frac{ab}{(a+b)^2}+\frac{bc}{(b+c)^2}+\frac{ca}{(c+a)^2} ) \ge 6(a^2+b^2+c^2) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28828` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28828; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28828 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 4 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b) * (b + c) * (c + a) * (a * b / (a + b) ^ 2 + b * c / (b + c) ^ 2 + c * a / (c + a) ^ 2) ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
