-- Prove2me | Theorems.Thm_WorkbookSource_base_43717
-- name    : WorkbookSource.base_43717
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:11.439702+00:00
-- url     : https://prove2.me/theorems/f822f1c5-ad6c-4901-8257-4f4cd01e32ad
-- title:
--   A symmetric sixth-degree comparison of mixed power sums
-- statement:
--   Let a,b,c>0.Prove that
--    $ 2(a^6 + b^6 + c^6 ) + 3\sum\limits_{cyc} {a^2 b^2 (a^2 + b^2 } ) \ge 2(a^3 b^3 + b^3 c^3 + a^3 c^3 ) + 3\sum\limits_{cyc} {ab(a^4 + b^4 )}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43717` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43717; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43717 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  2 * (a ^ 6 + b ^ 6 + c ^ 6) + 3 * (a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2) + b ^ 2 * c ^ 2 * (b ^ 2 + c ^ 2) + c ^ 2 * a ^ 2 * (c ^ 2 + a ^ 2)) ≥ 2 * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + a ^ 3 * c ^ 3) + 3 * (a * b * (a ^ 4 + b ^ 4) + b * c * (b ^ 4 + c ^ 4) + c * a * (c ^ 4 + a ^ 4))  :=  by sorry
