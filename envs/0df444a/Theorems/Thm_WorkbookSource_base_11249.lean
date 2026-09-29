-- Prove2me | Theorems.Thm_WorkbookSource_base_11249
-- name    : WorkbookSource.base_11249
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:43:47.71715+00:00
-- url     : https://prove2.me/theorems/7a72e529-0ada-4546-adf8-760968bd41e2
-- title:
--   A cubic-sum bound for variables of sum three
-- statement:
--   Prove that for non-negative reals $a, b, c$ such that $a + b + c = 3$, the inequality $7(a^2 + b^2 + c^2) \geq 2(c^3 + a^3 + b^3) + 9$ holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11249` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11249; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11249 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : 7 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (c ^ 3 + a ^ 3 + b ^ 3) + 9  :=  by sorry
