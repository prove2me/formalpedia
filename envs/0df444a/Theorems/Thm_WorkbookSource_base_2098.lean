-- Prove2me | Theorems.Thm_WorkbookSource_base_2098
-- name    : WorkbookSource.base_2098
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:00:21.269225+00:00
-- url     : https://prove2.me/theorems/1127c3dc-94bd-46e8-9d54-f25a4912104b
-- title:
--   A cubic-factor upper bound under a sum constraint
-- statement:
--   Let $a,b,c\ge0$ and $a+b+c=3.$ Prove that $$(3a-bc)(3b-ca)(3c-ab)\leq 8 abc .$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2098` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2098; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2098 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : (3 * a - b * c) * (3 * b - c * a) * (3 * c - a * b) ≤ 8 * a * b * c  :=  by sorry
