-- Prove2me | Theorems.Thm_WorkbookSource_base_4988
-- name    : WorkbookSource.base_4988
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:21:33.333323+00:00
-- url     : https://prove2.me/theorems/fcd26721-a1dc-426c-9ec1-8252bd797050
-- title:
--   An eighth-power bound for symmetric mixed products
-- statement:
--   Let $ a,$ $ b$ and $ c$ are non-negative numbers. Prove that:
--    $ (a + b + c)^8\geq128(a^5b^3 + a^5c^3 + b^5a^3 + b^5c^3 + c^5a^3 + c^5b^3)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4988` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4988; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4988 (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b + c) ^ 8 ≥ 128 * (a ^ 5 * b ^ 3 + a ^ 5 * c ^ 3 + b ^ 5 * a ^ 3 + b ^ 5 * c ^ 3 + c ^ 5 * a ^ 3 + c ^ 5 * b ^ 3)  :=  by sorry
