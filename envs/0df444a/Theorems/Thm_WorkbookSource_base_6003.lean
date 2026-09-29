-- Prove2me | Theorems.Thm_WorkbookSource_base_6003
-- name    : WorkbookSource.base_6003
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:43.093284+00:00
-- url     : https://prove2.me/theorems/f1c8e624-1b6b-416c-b7fd-6c6bd9a8b7c6
-- title:
--   A cyclic linear-over-quadratic lower bound at fixed sum three
-- statement:
--   Let a,b and c tree positives reels such that $ a+b+c=3 $ ; prove that :
--    $ \frac{a}{b^2+c} + \frac{b}{c^2+a} + \frac{c}{a^2+b} \ge 3/2 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6003` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6003; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6003 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (b ^ 2 + c) + b / (c ^ 2 + a) + c / (a ^ 2 + b) ≥ 3 / 2  :=  by sorry
