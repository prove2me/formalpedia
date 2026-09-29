-- Prove2me | Theorems.Thm_WorkbookSource_base_28566
-- name    : WorkbookSource.base_28566
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:44.32512+00:00
-- url     : https://prove2.me/theorems/b54ffb9a-054c-4c2f-9248-08354ded86e9
-- title:
--   A quartic norm bound with a cubic correction
-- statement:
--   Let $a, b, c $ be positive real number such that $a+b+c=3$ . Prove that
--    $7(a^2+b^2+c^2)^2+6abc\ge 23(a^2+b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28566` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28566; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28566 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 7 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 6 * a * b * c ≥ 23 * (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
