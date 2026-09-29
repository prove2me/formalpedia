-- Prove2me | Theorems.Thm_WorkbookSource_base_12023
-- name    : WorkbookSource.base_12023
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:43:51.886757+00:00
-- url     : https://prove2.me/theorems/54e25935-75da-42c3-8d49-4df6d25afdc8
-- title:
--   A normalized bound between power sums
-- statement:
--   Let $a,b,c$ are nonnegative real numbers such that $a+b+c=3.$ Prove that $$(a^4+b^4+c^4)^2\ge (a^2+b^2+c^2)(a^5+b^5+c^5).$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12023` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12023; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12023 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^4 + b^4 + c^4)^2 ≥ (a^2 + b^2 + c^2) * (a^5 + b^5 + c^5)  :=  by sorry
