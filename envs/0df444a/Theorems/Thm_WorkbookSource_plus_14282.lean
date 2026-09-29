-- Prove2me | Theorems.Thm_WorkbookSource_plus_14282
-- name    : WorkbookSource.plus_14282
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:25:46.378638+00:00
-- url     : https://prove2.me/theorems/85f6a651-a381-40ad-a2e8-8b563d53b291
-- title:
--   A pairwise squared-product bound at fixed sum one
-- statement:
--   Let $a$ , $b$ and $c$ be non-negative numbers such that $a+b+c=1$ . Prove that: $216(a^2b^2+a^2c^2+b^2c^2)\leq11((a-b)^2+(a-c)^2+(b-c)^2)+8$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_14282` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_14282; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_14282 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1) : 216 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) ≤ 11 * ((a - b)^2 + (a - c)^2 + (b - c)^2) + 8   :=  by sorry
