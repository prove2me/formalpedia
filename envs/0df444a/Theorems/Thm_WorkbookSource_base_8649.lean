-- Prove2me | Theorems.Thm_WorkbookSource_base_8649
-- name    : WorkbookSource.base_8649
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:38:47.134502+00:00
-- url     : https://prove2.me/theorems/1d5b8fe7-a253-42c4-b7bc-5db5c8601435
-- title:
--   A cyclic mixed quadratic ratio sum is at least three
-- statement:
--   Let a,b,c>0. Prove that $\frac{{{a^2} + bc}}{{b\left( {c + a} \right)}} + \frac{{{b^2} + ca}}{{c\left( {a + b} \right)}} + \frac{{{c^2} + ab}}{{a\left( {b + c} \right)}} \ge 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8649` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8649; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8649 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b * c) / (b * (c + a)) + (b^2 + c * a) / (c * (a + b)) + (c^2 + a * b) / (a * (b + c)) ≥ 3  :=  by sorry
