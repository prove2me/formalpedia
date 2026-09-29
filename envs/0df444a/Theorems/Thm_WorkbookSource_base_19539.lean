-- Prove2me | Theorems.Thm_WorkbookSource_base_19539
-- name    : WorkbookSource.base_19539
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:42:33.696459+00:00
-- url     : https://prove2.me/theorems/5dcb72ba-66e6-4a97-b1ce-1067c32eae57
-- title:
--   A cyclic cubic upper bound at fixed sum two
-- statement:
--   Let $a, b, c$ be nonnegative real numbers such that $a+b+c=2$ . Show that $$ a^3 + 2a^2b + 3abc \leq 8.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19539` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19539; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19539 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : a^3 + 2*a^2*b + 3*a*b*c ≤ 8  :=  by sorry
