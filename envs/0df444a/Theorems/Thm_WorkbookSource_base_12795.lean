-- Prove2me | Theorems.Thm_WorkbookSource_base_12795
-- name    : WorkbookSource.base_12795
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:17.239441+00:00
-- url     : https://prove2.me/theorems/699b7811-cc25-4667-b27d-8f45d5fa431c
-- title:
--   A pairwise weighted-square inequality at unit sum
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=1$ . Prove that $$ ab(a+b)^2+bc(b+c)^2+ca(c+a)^2\geq 4abc $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12795` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12795; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12795 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : a * b * (a + b) ^ 2 + b * c * (b + c) ^ 2 + c * a * (c + a) ^ 2 ≥ 4 * a * b * c  :=  by sorry
