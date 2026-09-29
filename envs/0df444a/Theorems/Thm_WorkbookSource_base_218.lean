-- Prove2me | Theorems.Thm_WorkbookSource_base_218
-- name    : WorkbookSource.base_218
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:07.648029+00:00
-- url     : https://prove2.me/theorems/738bcf54-9097-4e8b-b56a-6df36b4a459f
-- title:
--   A quadratic rational sum bounded by the squared total
-- statement:
--   If $ a,$ $ b,$ $ c$ are positive real numbers, then
--    $ \frac{a(b+c)}{a^2+2bc}+\frac{b(c+a)}{b^2+2ca}+\frac{c(a+b)}{c^2+2ab}+1 \le \frac{(a+b+c)^2}{ab+bc+ca}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_218` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_218; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_218 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c) / (a ^ 2 + 2 * b * c) + b * (c + a) / (b ^ 2 + 2 * c * a) + c * (a + b) / (c ^ 2 + 2 * a * b) + 1) ≤ (a + b + c) ^ 2 / (a * b + b * c + a * c)  :=  by sorry
