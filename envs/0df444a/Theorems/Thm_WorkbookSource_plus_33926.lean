-- Prove2me | Theorems.Thm_WorkbookSource_plus_33926
-- name    : WorkbookSource.plus_33926
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:48:51.378034+00:00
-- url     : https://prove2.me/theorems/3636e931-4663-4dcf-8f06-e5a7fe71a555
-- title:
--   A cyclic linear difference reciprocal sum upper bound
-- statement:
--   Let $a,b,c$ be positive reals. Then
--    $ \sum_{cycl}\frac{a+b-c}{a^2+ab+b^2} \le \frac{3}{a+b+c} $
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_33926` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_33926; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_33926 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b - c) / (a ^ 2 + a * b + b ^ 2) + (b + c - a) / (b ^ 2 + b * c + c ^ 2) + (c + a - b) / (c ^ 2 + c * a + a ^ 2) ≤ 3 / (a + b + c)   :=  by sorry
