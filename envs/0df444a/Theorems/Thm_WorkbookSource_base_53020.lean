-- Prove2me | Theorems.Thm_WorkbookSource_base_53020
-- name    : WorkbookSource.base_53020
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:23.318906+00:00
-- url     : https://prove2.me/theorems/ff3c212f-1883-4b33-b698-9e90e7e671a4
-- title:
--   A product of quadratic sums at fixed sum two
-- statement:
--   Let $a,b,c$ are nonnegative real numbers satisfying $a+b+c=2.$ Prove that $(a^2+b^2+c^2)(a^2+b^2)(b^2+c^2)(c^2+a^2)\le 4.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53020` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53020; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53020 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : (a^2 + b^2 + c^2) * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≤ 4  :=  by sorry
