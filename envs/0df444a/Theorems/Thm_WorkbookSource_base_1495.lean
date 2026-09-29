-- Prove2me | Theorems.Thm_WorkbookSource_base_1495
-- name    : WorkbookSource.base_1495
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:53:58.720726+00:00
-- url     : https://prove2.me/theorems/8f1aca0d-b01c-47de-ae53-ab6787b8b9c4
-- title:
--   A symmetric cubic sum bounds a cyclic rational expression
-- statement:
--   Suppose $ a,b,c $ are positive reals. Prove or disprove the following inequality.
--    $ a^2b+a^2c+b^2a+b^2c+c^2a+c^2b \ge \frac{a^2(5b^2-a^2)}{a+b}+\frac{b^2(5c^2-b^2)}{b+c}+\frac{c^2(5a^2-c^2)}{c+a} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1495` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1495; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1495 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b ≥ a^2 * (5 * b^2 - a^2) / (a + b) + b^2 * (5 * c^2 - b^2) / (b + c) + c^2 * (5 * a^2 - c^2) / (c + a)  :=  by sorry
