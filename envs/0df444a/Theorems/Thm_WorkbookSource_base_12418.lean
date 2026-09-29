-- Prove2me | Theorems.Thm_WorkbookSource_base_12418
-- name    : WorkbookSource.base_12418
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:43:12.589985+00:00
-- url     : https://prove2.me/theorems/beeca838-8d10-45a0-b350-131813f65967
-- title:
--   A cyclic mixed cubic ratio bounds a normalized quadratic sum
-- statement:
--   Prove that for all positive real numbers $ a,b$ and $ c$ ,
--    $ \frac {ab^{2}}{c^{2}} + \frac {bc^{2}}{a^{2}} + \frac {ca^{2}}{b^{2}} + a + b + c \ge \frac {6(a^{2} + b^{2} + c^{2})}{a + b + c}
--    I can rewrite the inequality :
--    $ \sum_{cyc} (a-b)^2(\frac{c}{a}-\frac{2}{a+b+c}) \geq 0$
--    But I don't know how to continue
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12418` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12418; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12418 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b ^ 2 / c ^ 2 + b * c ^ 2 / a ^ 2 + c * a ^ 2 / b ^ 2 + a + b + c) ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c)  :=  by sorry
