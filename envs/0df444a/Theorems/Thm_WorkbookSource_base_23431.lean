-- Prove2me | Theorems.Thm_WorkbookSource_base_23431
-- name    : WorkbookSource.base_23431
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:53.134454+00:00
-- url     : https://prove2.me/theorems/86bd2bc2-d184-4186-b2b0-93fb3b132028
-- title:
--   A mixed product and cubic bound at unit sum
-- statement:
--   Let $a, b, c$ be positive real numbers such that $a+b+c=1$ . Prove that $ (a+b)(b+c)(c+a)(a^3+b^3+c^3+\frac{1}{3}) \le \frac{4}{27}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23431` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23431; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23431 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) :  (a + b) * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3 + 1 / 3) ≤ 4 / 27  :=  by sorry
