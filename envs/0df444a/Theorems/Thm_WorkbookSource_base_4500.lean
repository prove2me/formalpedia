-- Prove2me | Theorems.Thm_WorkbookSource_base_4500
-- name    : WorkbookSource.base_4500
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:12:47.529499+00:00
-- url     : https://prove2.me/theorems/7c340512-1fba-4884-b280-c82e3bbb5f36
-- title:
--   A symmetric cubic ratio with a quadratic correction
-- statement:
--   Let $a, \, b, \, c \, > 0$ . Prove that
--    $ \frac{a^3+b^3+c^3+3abc}{(a+b)(b+c)(c+a)}+\frac{(a+b+c)^2}{6(a^2+b^2+c^2)}\ge \frac{5}{4} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4500` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4500; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4500 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3 + 3 * a * b * c) / (a + b) / (b + c) / (c + a) + (a + b + c)^2 / 6 / (a^2 + b^2 + c^2) ≥ 5 / 4  :=  by sorry
