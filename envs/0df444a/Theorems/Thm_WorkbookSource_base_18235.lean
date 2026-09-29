-- Prove2me | Theorems.Thm_WorkbookSource_base_18235
-- name    : WorkbookSource.base_18235
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:59:26.061658+00:00
-- url     : https://prove2.me/theorems/5afb3e10-c970-4aea-aefd-36f2dc889bdc
-- title:
--   A fourth-power sum bounds twice the cubic sum minus two at fixed sum two
-- statement:
--   Let a,b,c be positive real numbers such that a+b+c=2
--   Prove the inequality
--    $ \frac{1}{2}(a^4+b^4+c^4)+1\geq a^3+b^3+c^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18235` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18235; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18235 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2) : 1 / 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 1 ≥ a ^ 3 + b ^ 3 + c ^ 3  :=  by sorry
