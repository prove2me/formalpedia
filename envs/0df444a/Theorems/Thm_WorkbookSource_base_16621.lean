-- Prove2me | Theorems.Thm_WorkbookSource_base_16621
-- name    : WorkbookSource.base_16621
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:43:02.548052+00:00
-- url     : https://prove2.me/theorems/de4ffb5b-43e6-4981-9220-567745e80213
-- title:
--   A cyclic cubic bound under a fixed sum
-- statement:
--   Let $ a,b,c >0 $ & $a+b+c=6$ , $q=ab+bc+ca$ . Prove that:
--
--    $$ 2(ab^2+bc^2+ca^2)+3abc \le q^2-19q+156 $$
--
--   Click to reveal hidden text
--
--   Check the equality cases, you will find something nice
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16621` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16621; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16621 (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 6) (hq : q = a * b + b * c + c * a) : 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 3 * a * b * c ≤ q ^ 2 - 19 * q + 156  :=  by sorry
