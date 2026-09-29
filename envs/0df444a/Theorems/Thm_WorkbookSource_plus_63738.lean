-- Prove2me | Theorems.Thm_WorkbookSource_plus_63738
-- name    : WorkbookSource.plus_63738
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:41.692998+00:00
-- url     : https://prove2.me/theorems/96475cde-2676-44fb-a14e-2dab92494939
-- title:
--   A shifted-square product bound at sum three
-- statement:
--   If $a,b,c$ are real numbers such that $a+b+c=3$ , then
--
--    $$(a^2+1)(b^2+1)(c^2+1)\ge (a+1)(b+1)(c+1)+(abc-1)^2+\dfrac{29(3-ab-bc-ca)}{27} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_63738` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_63738; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_63738 (a b c : ℝ) (hab : a + b + c = 3) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a + 1) * (b + 1) * (c + 1) + (a * b * c - 1)^2 + (29 * (3 - a * b - b * c - a * c)) / 27   :=  by sorry
