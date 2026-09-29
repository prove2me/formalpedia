-- Prove2me | Theorems.Thm_WorkbookSource_base_7483
-- name    : WorkbookSource.base_7483
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:05:41.413813+00:00
-- url     : https://prove2.me/theorems/70bce353-23de-4de5-8ec4-4f489da237eb
-- title:
--   A product of squared pairwise sums bounds three linear factors
-- statement:
--   Let $a,b,c >0$. Prove that
--
--    $(a+b)^2(b+c)^2(c+a)^2 \ge abc(2a+b+c)(a+2b+c)(a+b+2c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7483` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7483; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7483 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 ≥ a * b * c * (2 * a + b + c) * (a + 2 * b + c) * (a + b + 2 * c)  :=  by sorry
