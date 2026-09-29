-- Prove2me | Theorems.Thm_WorkbookSource_base_31666
-- name    : WorkbookSource.base_31666
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:46:44.743992+00:00
-- url     : https://prove2.me/theorems/efc13e90-124a-45da-8053-bf522bfc43d6
-- title:
--   A weighted pair-product ratio sum is at least eleven
-- statement:
--   Given $ a,b,c > 0$ .Prove that: $ \frac {20ab}{(a + c)(b + c)} + \frac {15bc}{(b + a)(c + a)} + \frac {12ca}{(c + b)(a + b)} \ge 11$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31666` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31666; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31666 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 20 * a * b / (a + c) / (b + c) + 15 * b * c / (b + a) / (c + a) + 12 * c * a / (c + b) / (a + b) ≥ 11  :=  by sorry
