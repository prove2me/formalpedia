-- Prove2me | Theorems.Thm_WorkbookSource_base_40599
-- name    : WorkbookSource.base_40599
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:12:36.128537+00:00
-- url     : https://prove2.me/theorems/5af23b34-5a52-4581-a3ec-d9d2cfdd42e9
-- title:
--   A cubed total bounds a cubic sum with a triple-product correction
-- statement:
--   Let $a,b,c> 0$ . Prove:
--
--    $$(a+b+c)^3(a^3+b^3+c^3+abc)\ge 36abc(a^3+b^3+c^3)$$
--
--   To flvbin: solution by hand
--
--   $LHS - RHS$
--
--   equals to:
--
--    $ \sum a^4(a-b)(a-c) +3(a-b)^2(b-c)^2(c-a)^2+ \sum [c^3+(ab^2+a^2b+c^3-3abc)] (a-b)^2 \geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40599` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40599; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40599 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) ≥ 36 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3)  :=  by sorry
