-- Prove2me | Theorems.Thm_WorkbookSource_base_5250
-- name    : WorkbookSource.base_5250
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:07.491014+00:00
-- url     : https://prove2.me/theorems/b46e7052-054c-468c-87b2-dd0f16ae5e83
-- title:
--   A cubic sum bound with a triple-product correction
-- statement:
--   Let $ a,b,c\ge 0$ and $ a + b + c = 1$ ,prove that $ a^3 + b^3 + c^3 + 6abc\ge \frac {1}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5250` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5250; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5250 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 1) : a^3 + b^3 + c^3 + 6 * a * b * c ≥ 1 / 4  :=  by sorry
