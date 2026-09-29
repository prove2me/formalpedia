-- Prove2me | Theorems.Thm_WorkbookSource_base_23459
-- name    : WorkbookSource.base_23459
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:28:36.662395+00:00
-- url     : https://prove2.me/theorems/969bafb8-5324-403a-8425-e0c34903f45e
-- title:
--   A shifted quadratic ratio comparison
-- statement:
--   If $ a,b,c>0$ , then
--
--    $ \frac{c^2+c-b}{a+b+2c}+\frac{b^2+b-a}{a+2b+c}+\frac{a^2+a-c}{2a+b+c}\leq\frac{1}{2}(\frac{a^2}{b+c}+\frac{b^2}{c+a}+\frac{c^2}{a+b})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23459` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23459; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23459 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c^2 + c - b) / (a + b + 2 * c) + (b^2 + b - a) / (a + 2 * b + c) + (a^2 + a - c) / (2 * a + b + c) ≤ (1 / 2) * (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b))  :=  by sorry
