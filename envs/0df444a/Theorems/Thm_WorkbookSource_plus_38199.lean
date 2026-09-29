-- Prove2me | Theorems.Thm_WorkbookSource_plus_38199
-- name    : WorkbookSource.plus_38199
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:06.114252+00:00
-- url     : https://prove2.me/theorems/b66b8635-29f6-4eae-b3f9-bb97e742abaa
-- title:
--   A squared symmetric cubic expression is bounded by a cubic square sum
-- statement:
--   Let a,b,c>0, prove
--
--    $ \left(abc + (a + b)(b + c)(c + a) \right)^2 \le 3(a^2 + b^2 + c^2)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_38199` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_38199; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_38199 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * c + (a + b) * (b + c) * (c + a))^2 ≤ 3 * (a^2 + b^2 + c^2)^3   :=  by sorry
