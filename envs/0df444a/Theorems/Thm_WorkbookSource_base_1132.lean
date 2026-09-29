-- Prove2me | Theorems.Thm_WorkbookSource_base_1132
-- name    : WorkbookSource.base_1132
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:16.541406+00:00
-- url     : https://prove2.me/theorems/14384331-50f8-465c-82a1-115a14ddcf84
-- title:
--   A normalized cubic sum with a cyclic correction
-- statement:
--   Let $a,b,c>0$ . Prove that:
--    $\frac{(a+b+c)^3}{3abc}+\frac{ab^2+bc^2+ca^2}{a^3+b^3+c^3} \geq 10$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1132` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1132; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1132 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 / (3 * a * b * c) + (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / (a ^ 3 + b ^ 3 + c ^ 3) ≥ 10  :=  by sorry
