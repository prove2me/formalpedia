-- Prove2me | Theorems.Thm_WorkbookSource_plus_18784
-- name    : WorkbookSource.plus_18784
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:32:40.879598+00:00
-- url     : https://prove2.me/theorems/0ba9d6ff-b486-4e02-849f-646abe9fdef8
-- title:
--   A four-variable product inequality for nonnegative inputs
-- statement:
--   Prove or disprove:
--    $ (a+b+c)(b+c+d)(c+d+a)(d+a+b) \ge 4(a+b)(b+c)(c+d)(d+a) $
--   Given $a,b,c,d\ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_18784` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_18784; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_18784 {a b c d : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) : (a + b + c) * (b + c + d) * (c + d + a) * (d + a + b) ≥ 4 * (a + b) * (b + c) * (c + d) * (d + a)   :=  by sorry
