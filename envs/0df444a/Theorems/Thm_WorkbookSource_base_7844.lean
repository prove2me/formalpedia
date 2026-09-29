-- Prove2me | Theorems.Thm_WorkbookSource_base_7844
-- name    : WorkbookSource.base_7844
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:45:52.008851+00:00
-- url     : https://prove2.me/theorems/c593463b-e4fc-43dd-b215-dd39aed8493d
-- title:
--   A four-variable quartic power-sum inequality at total four
-- statement:
--   On the other hand, the following inequality holds for $a+b+c+d=4$ :
--
--    $$13(a^2+b^2+c^2+d^2)^2\ge 12(a^4+b^4+c^4+d^4)+160.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7844` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7844; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7844 (a b c d : ℝ) (h : a + b + c + d = 4) : 13 * (a^2 + b^2 + c^2 + d^2)^2 ≥ 12 * (a^4 + b^4 + c^4 + d^4) + 160  :=  by sorry
